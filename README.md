# Collection

This package provides support for "functional" style programming with Go
collections (maps and slices). A typical functional programming library is based
on higher-order functions like MAP defined over sequences, which naturally
correspond to slices in Go. This library, however, uses map[K]V-s as the basic
types and defines operations on slices in terms of operations on maps.

The goal of this library is to define a reasonable set of higher-order functions
in terms of a minimal set of "basic" primitives, without regard to efficiency.

