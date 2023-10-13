package collection

import "testing"
import "slices"
import "fmt"

func TestExists(t *testing.T) {
	empty := map[int]int{}
	if Exists(empty, func(k int, v int) bool { return true }) {
		t.Errorf("Something exists in an empty map.")
	}
	if !Exists(map[int]int{0:1}, func(k int, v int) bool { return k == 0 }) {
		t.Errorf("Existing key does not exist in a singleton map.")
	}
	if !Exists(map[int]int{2:0, 0:1}, func(k int, v int) bool { return k == 0 }) {
		t.Errorf("Existing key does not exist.")
	}
	if Exists(map[int]int{0:1}, func(k int, v int) bool { return k == 2 }) {
		t.Errorf("Non-existing key exists in a singleton map.")
	}
	if Exists(map[int]int{3:0, 0:1}, func(k int, v int) bool { return k == 2 }) {
		t.Errorf("Non-existing key exists.")
	}
}

func TestForall(t *testing.T) {
	empty := map[int]int{}
	if !Forall(empty, func(k int, v int) bool { return false }) {
		t.Errorf("Predicate does not hold on an empty set.")
	}
	if Forall(map[int]int{1:1, 0:1}, func(k int, v int) bool { return k != 0 }) {
		t.Errorf("Forall misses predicate violation.")
	}
}

func TestZip(t *testing.T) {
	maps := []map[int]int {
		{},
		{0:0},
		{0:0, 1:1},
	}
	for _, m := range maps {
		if !Equal(m, Zip(Unroll(m))) {
			t.Errorf("Zip(Unroll(%v)) == %v.", m, Zip(Unroll(m)))
		}
	}
}

func TestSort(t *testing.T) {
	arrays := [][]int {
		{},
		{0},
		{0, 1},
		{1, 0},
		{1, 3, 2, 1, 0},
	}
	var quicksort func(a []int) []int
	quicksort = func(a []int) []int { // A "functional" version of quicksort.
		if len(a) == 0 {
			return a
		} else {
			return append(append(
				quicksort(Filter(a[1:], func(_ int, v int) bool { return v <= a[0] })), a[0]),
				quicksort(Filter(a[1:], func(_ int, v int) bool { return v  > a[0] }))...)
		}
	}
	for i, s := range arrays {
		c := make([]int, len(s))
		copy(c, s)
		slices.Sort(c)
		for j, v := range quicksort(arrays[i]) {
			if c[j] != v {
				fmt.Printf("original: %v\n", arrays[i])
				fmt.Printf("sorted:   %v\n", c)
				fmt.Printf("q-sorted: %v\n", quicksort(arrays[i]))
				t.Errorf("Wrong sort at %d.", j)
			}
		}
	}
}

func TestJoin(x *testing.T) {
	type tt struct {
		set0         []int
		set1         []int
		union        []int
		intersection []int
	}
	tests := []tt {
		{ set0: []int{}, set1: []int{}, union: []int{}, intersection: []int{} },
		{ set0: []int{}, set1: []int{0}, union: []int{0}, intersection: []int{} },
		{ set0: []int{1, 2, 3}, set1: []int{2, 3, 4}, union: []int{1, 2, 3, 4}, intersection: []int{2, 3} },
	}
	for _, t := range(tests) {
		if !Equal(Join(Roll(t.set0, true), Roll(t.set1, true)), Roll(t.union, true)) {
			x.Errorf("Join(%v, %v) == %v", t.set0, t.set1, Join(Roll(t.set0, true), Roll(t.set1, true)))
		}
		if !Equal(Meet(Roll(t.set0, true), Roll(t.set1, true)), Roll(t.intersection, true)) {
			x.Errorf("Meet(%v, %v) == %v", t.set0, t.set1, Meet(Roll(t.set0, true), Roll(t.set1, true)))
		}
	}
}
