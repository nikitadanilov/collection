// Copyright 2023 Nikita Danilov. All rights reserved.

// Use of this source code is governed by GNU LESSER GENERAL PUBLIC LICENSE,
// version 2.1 that can be found in the LICENSE file.

// This file provides support for "functional" style programming with Go
// collections (maps and slices). A typical functional programming library is
// based on higher-order functions like MAP defined over sequences, which
// naturally correspond to slices in Go. This library, however, uses map[K]V as
// the basic types and defines operations on slices in terms of operations on
// maps.
//
// The goal of this library is to define a reasonable set of higher-order
// functions in terms of a minimal set of "basic" primitives, without regard to
// efficiency.
package collection

import "slices"
import "cmp"
import "fmt"

// Polymorphic pair type. Graph() and Ungraph() convert between a map and its
// "graph", that is, the slice of key-value pairs.
type Pair[A, B any] struct {
	p0 A
	p1 B
}

// The type of predicate functions.
type Pred[K, V any] func(K, V) bool

// A function adapter, that from a function f(a), builds a function F(a, b) :=
// f(a), ignoring its second argument.
func A0[A, B, C any](f func(A) C) func(A, B) C {
	return func(a A, _ B) C {
		return f(a)
	}
}

// A function adapter, that from a function f(b), builds a function F(a, b) :=
// f(b), ignoring its first argument.
func A1[A, B, C any](f func(B) C) func(A, B) C {
	return func(_ A, b B) C {
		return f(b)
	}
}

// The same as A0(), but for the functions that do not return anything. A
// separate adapter is needed, because you cannot generalise over void return
// type in Go.
func A0V[A, B any](f func(A)) func(A, B) {
	return func(a A, _ B) {
		f(a)
	}
}

// The same as A1(), but for the functions that do not return anything.
func A1V[A, B any](f func(B)) func(A, B) {
	return func(_ A, b B) {
		f(b)
	}
}

// A function adapater, substitures a given value as the second argument of a
// binary function, to produce a singular function.
func S0[A, B, C any](f func(A, B) C, a A) func(B) C {
	return func(b B) C {
		return f(a, b)
	}
}

// A function adapater, substitures a given value as the first argument of a
// binary function, to produce a singular function.
func S1[A, B, C any](f func(A, B) C, b B) func(A) C {
	return func(a A) C {
		return f(a, b)
	}
}

// From 2 functions f:A->B and g:A->C, builds a function (f, g):A->B*C.
func Prod[A, B, C any](f func(A) B, g func(A) C) func(A) (B, C) {
	return func(a A) (B, C) {
		return f(a), g(a)
	}
}

// From 2 functions f:A0->B0 and g:A1->B1, builds a function f*g:A0*A1->B0*B1
func BiProd[A0, A1, B0, B1 any](f func(A0) B0, g func(A1) B1) func(a0 A0, a1 A1) (B0, B1) {
	return func(a0 A0, a1 A1) (B0, B1) {
		return f(a0), g(a1)
	}
}

// Polymorphic identity function.
func Id[A any](a A) A {
	return a
}

// Curries f:A*B->C to Curry(f):A->(B->C).
func Curry[A, B, C any](f func(A, B) C) func(A) func(B) C {
	return func(a A) func(B) C {
		return func(b B) C {
			return f(a, b)
		}
	}
}

// Returns a key-value pair from a given map satisfying the given predicate, if
// any. Otherwise, returns a pair of zero values.
func Any[K comparable, V any](m map[K]V, f Pred[K, V]) (k K, v V, ok bool) {
	for key, val := range m {
		if f(key, val) {
			return key, val, true
		}
	}
	return k, v, false
}

// Iterates a given function over a map.
func Iterate[K comparable, V any](m map[K]V, f func(K, V)) {
	for key, val := range m {
		f(key, val)
	}
}

// Returns a submap of a given map, consisting of all key-value pairs,
// satisfying the predicate.
func All[K comparable, V any](m map[K]V, f Pred[K, V]) map[K]V {
	r := make(map[K]V, len(m))
	Iterate(m, func(k K, v V) {
		if f(k, v) {
			r[k] = v
		}
	})
	return r
}

// Reports whether any key-value pair in a given map satisfies a given predicate.
func Exists[K comparable, V any](m map[K]V, f Pred[K, V]) bool {
	_, _, found := Any(m, f)
	return found
}

// Reports whether all key-value pair in a given map satisfy a given predicate.
func Forall[K comparable, V any](m map[K]V, f Pred[K, V]) bool { /* Frege made me do it. */
	return !Exists(m, func(key K, val V) bool { return !f(key, val) })
}

// Builds from a given slices, the map using values in the slice as the keys,
// and a given token as the constant value. The order of the valuesin the slice
// is lost. A typical token would be "true" or "struct{}{}".
func Roll[K comparable, V any](s []K, token V) map[K]V {
	m := make(map[K]V, len(s))
	Iterate(m, func(k K, _ V) {
		m[k] = token
	})
	return m
}

// Converts a map into slices of the map's keys and values.
func Unroll[K comparable, V any](m map[K]V) (k []K, v []V) {
	Iterate(m, func(key K, val V) {
		k = append(k, key)
		v = append(v, val)
	})
	return k, v
}

// Slice of maps keys.
func Keys[K comparable, V any](m map[K]V) []K {
	keys, _ := Unroll(m)
	return keys
}

// Slice of maps values.
func Values[K comparable, V any](m map[K]V) []V {
	_, values := Unroll(m)
	return values
}

// Converts a slice into the map of slice values indexed by integers.
func Enum[V any](s []V) map[int]V {
	m := make(map[int]V, len(s))
	for i, v := range s {
		m[i] = v
	}
	return m
}

// Converts a map with orderable keys in a slice containing the same values in
// the same order as the map.
func Unenum[K interface {
	comparable
	cmp.Ordered
}, V any](m map[K]V) []V {
	r := make([]V, len(m))
	keys := Keys(m)
	slices.Sort(keys)
	for i := 0; i < len(m); i++ {
		r[i] = m[keys[i]]
	}
	return r
}

// Returns a slice of key-value pairs for a given map.
func Graph[K comparable, V any](m map[K]V) []Pair[K, V] {
	s := make([]Pair[K, V], len(m))
	Iterate(m, func(k K, v V) {
		s = append(s, Pair[K, V]{p0: k, p1: v})
	})
	return s
}

// Reverse of Graph(). Converts a slice of pairs into the map containing the
// same key-value pairs.
func Ungraph[K comparable, V any](s []Pair[K, V]) map[K]V {
	m := make(map[K]V, len(s))
	for _, p := range s {
		m[p.p0] = p.p1
	}
	return m
}

// Returns the inverse of a given map (teh keys become values and the values
// become keys).
func Inverse[K, V comparable](m map[K]V) (map[V]K, bool) {
	unique := true
	r := make(map[V]K, len(m))
	Iterate(m, func(k K, v V) {
		if _, found := r[v]; !found {
			unique = false
		}
		r[v] = k
	})
	return r, unique
}

// Given a slice of keys and a slice of values, builds the map containign the
// matching key-value pairs.
func Zip[K comparable, V any](keys []K, vals []V) map[K]V {
	m := make(map[K]V, len(keys))
	for idx, k := range keys {
		m[k] = vals[idx]
	}
	return m
}

// Applies a given function to the key-value pairs of a given map, and returns
// the map of results.
func Map[K0, K1 comparable, V0, V1 any](m map[K0]V0, f func(K0, V0) (K1, V1)) map[K1]V1 {
	r := make(map[K1]V1, len(m))
	Iterate(m, func(k K0, v V0) {
		kk, vv := f(k, v)
		r[kk] = vv
	})
	return r
}

// Fold (https://en.wikipedia.org/wiki/Fold_(higher-order_function)).
func Fold[V0 any, V1 any](s []V0, init V1, f func(int, V0, V1) V1) V1 {
	fold := init
	for i, v := range s {
		fold = f(i, v, fold)
	}
	return fold
}

// Reports whetherone map is a submap of another.
func Sub[K, V comparable](m0, m1 map[K]V) bool {
	return len(m0) <= len(m1) && Forall(m0, func(k K, v V) bool { v1, found := m1[k]; return found && v == v1 })
}

// Reports whether two maps are equal.
func Equal[K, V comparable](m0, m1 map[K]V) bool { // Sub(m0, m1) && Sub(m1, m0)
	return len(m0) == len(m1) && Sub(m0, m1)
}

// Given a sequence of maps, builds a map that maps any key present in any map
// in the sequence to the slice of all values (with duplicates), the key has in
// the maps of the sequence.
func Collect[K comparable, V any](ms ...map[K]V) map[K][]V {
	r := make(map[K][]V)
	for _, m := range ms {
		Iterate(m, func(k K, v V) {
			r[k] = append(r[k], v)
		})
	}
	return r
}

func common[K any, V comparable](k K, vs []V) (K, V) {
	if len(vs) == 0 {
		panic("At least one element is needed.")
	}
	for i := 1; i < len(vs); i++ {
		if vs[i] != vs[0] {
			panic(fmt.Sprintf("Contradictory values for key %v: %v != %v @%v", k, vs[0], vs[i], i))
		}
	}
	return k, vs[0]
}

// Builds the union (in the sense of a sets of key-value pairs) of a sequence of
// maps. The maps in the sequence must never map the same key to different
// values. This funciton panics if this consistency condition is violated.
func Join[K, V comparable](ms ...map[K]V) map[K]V {
	return Map(Collect(ms...), common[K, V])
}

// Builds the intersection (in the sense of a sets of key-value pairs) of a sequence of
// maps. The maps in the sequence must never map the same key to different
// values. This funciton panics if this consistency condition is violated.
func Meet[K, V comparable](ms ...map[K]V) map[K]V {
	return Map(All(Collect(ms...), func(k K, vs []V) bool { return len(vs) == len(ms) }), common[K, V])
}

// Filter (https://en.wikipedia.org/wiki/Filter_(higher-order_function)).
func Filter[V any](s []V, f Pred[int, V]) []V {
	return Unenum(All(Enum(s), f)) // "Value of everything and cost of nothing."
}

// Composes two maps as functions (or relations).
func Compose[A, B comparable, C any](m0 map[A]B, m1 map[B]C) map[A]C {
	r := make(map[A]C, len(m0))
	Iterate(m0, func(a A, b B) {
		if c, got := m1[b]; got {
			r[a] = c
		}
	})
	return r
}

// Returns the bag (multi-set) union of a given sequence of maps.
func Bag[K, V comparable](ms ...map[K]V) map[K]map[V]bool {
	return Map[K, K, []V, map[V]bool](Collect(ms...), BiProd[K, []V, K, map[V]bool](Id[K], S1[[]V, bool](Roll, true)))
}

// Given a slice, returns the map, mapping each unique element of the slice to
// the positive integer count of the number of element's occurrences in the
// slice.
func Count[V comparable](s []V) map[V]int {
	return Map(Collect(Unenum(Map(Enum(s), func(i int, v V) (int, map[V]int) { return i, map[V]int{v: i} }))...), func(v V, is []int) (V, int) { return v, len(is) })
}

// A "functional" version of quicksort.
func Quicksort[T cmp.Ordered](a []T) []T {
	if len(a) == 0 {
		return a
	} else {
		return append(append(
			Quicksort(Filter(a[1:], func(_ int, v T) bool { return v <= a[0] })), a[0]),
			Quicksort(Filter(a[1:], func(_ int, v T) bool { return v > a[0] }))...)
	}
}
