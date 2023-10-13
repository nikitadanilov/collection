package collection

import "slices"
import "cmp"
import "fmt"

type Pair[A, B any] struct {
	p0 A
	p1 B
}

type Pred[K, V any] func(key K, val V) bool

func Any[K comparable, V any](m map[K]V, f Pred[K, V]) (k K, v V, ok bool) {
	for key, val := range m {
		if f(key, val) {
			return key, val, true
		}
	}
	return k, v, false
}

func All[K comparable, V any](m map[K]V, f Pred[K, V]) map[K]V {
	r := make(map[K]V, len(m))
	for k, v := range m {
		if f(k, v) {
			r[k] = v
		}
	}
	return r
}

func Exists[K comparable, V any](m map[K]V, f Pred[K, V]) bool {
	_, _, found := Any(m, f)
	return found
}

func Forall[K comparable, V any](m map[K]V, f Pred[K, V]) bool { /* Frege made me do it. */
	return !Exists(m, func(key K, val V) bool { return !f(key, val) })
}

func Roll[K comparable, V any](s []K, token V) map[K]V {
	m := make(map[K]V, len(s))
	for _, k := range s {
		m[k] = token
	}
	return m
}

func Unroll[K comparable, V any](m map[K]V) (k []K, v []V) {
	for key, val := range m {
		k = append(k, key)
		v = append(v, val)
	}
	return k, v
}

func Keys[K comparable, V any](m map[K]V) []K {
	keys, _ := Unroll(m)
	return keys
}

func Values[K comparable, V any](m map[K]V) []V {
	_, values := Unroll(m)
	return values
}

func Enum[V any](s []V) map[int]V {
	m := make(map[int]V, len(s))
	for i, v := range s {
		m[i] = v
	}
	return m
}

func Unenum[K interface{comparable; cmp.Ordered}, V any](m map[K]V) []V {
	r := make([]V, len(m))
	keys := Keys(m)
	slices.Sort(keys)
	for i := 0; i < len(m); i++ {
		r[i] = m[keys[i]]
	}
	return r
}

func Graph[K comparable, V any](m map[K]V) []Pair[K, V] {
	s := make([]Pair[K, V], len(m))
	for k, v := range m {
		s = append(s, Pair[K, V]{p0: k, p1: v})
	}
	return s
}

func Ungraph[K comparable, V any](s []Pair[K, V]) map[K]V  {
	m := make(map[K]V, len(s))
	for _, p := range s {
		m[p.p0] = p.p1
	}
	return m
}

func Inverse[K, V comparable](m map[K]V) (map[V]K, bool) {
	unique := true
	r := make(map[V]K, len(m))
	for k, v := range(m) {
		if _, found := r[v]; !found {
			unique = false
		}
		r[v] = k
	}
	return r, unique
}

func Zip[K comparable, V any](keys []K, vals []V) map[K]V {
	m := make(map[K]V, len(keys))
	for idx, k := range keys {
		m[k] = vals[idx]
	}
	return m
}

func Map[K0, K1 comparable, V0, V1 any](m map[K0]V0, f func(key K0, val V0) (K1, V1)) map[K1]V1 {
	r := make(map[K1]V1, len(m))
	for k, v := range m {
		kk, vv := f(k, v)
		r[kk] = vv
	}
	return r
}

func Fold[V0 any, V1 any](s []V0, init V1, f func(idx int, val V0, accum V1) V1) V1 {
	fold := init
	for i, v := range s {
		fold = f(i, v, fold)
	}
	return fold
}

func Sub[K, V comparable](m0, m1 map[K]V) bool {
	return len(m0) <= len(m1) && Forall(m0, func(k K, v V) bool { v1, found := m1[k]; return found && v == v1 })
}

func Equal[K, V comparable](m0, m1 map[K]V) bool { // Sub(m0, m1) && Sub(m1, m0)
	return len(m0) == len(m1) && Sub(m0, m1)
}

func Collect[K comparable, V any](ms ...map[K]V) map[K][]V {
	r := make(map[K][]V)
	for _, m := range ms {
		for k, v := range(m) {
			r[k] = append(r[k], v)
		}
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

func Join[K, V comparable](ms ...map[K]V) map[K]V {
	return Map(Collect(ms...), common[K, V])
}

func Meet[K, V comparable](ms ...map[K]V) map[K]V {
	return Map(All(Collect(ms...), func(k K, vs []V) bool { return len(vs) == len(ms) }), common[K, V])
}

func Filter[V any](s []V, f Pred[int, V]) []V {
	return Unenum(All(Enum(s), f)) // "Value of everything and cost of nothing."
}
