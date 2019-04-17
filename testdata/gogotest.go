package main

import (
	"fmt"
	"time"
)

const (
	alsoTheAnswer = answer
	answer        = 42
)

type answerT int

const (
	typedAnswer answerT = alsoTheAnswer
)

func swap(x, y int) (int, int) {
	return y, x
}

func sum(x, y int) int {
	return x + y
}

func square(x int) int {
	return x * x
}

func pair(z int) (int, int) {
	return z, z
}

type Foo struct {
	X int
	Y string
}

func (f Foo) Bar() string {
	return fmt.Sprintf("%d, %s", f.X, f.Y)
}

type Baz struct {
	Z int
}

func (b *Baz) SetZ(z int) {
	b.Z = z
}

type Quux struct {
	Q string
}

func (q Quux) Whatever() string {
	return q.Q + ", whatever"
}

type MultiLevel struct {
	F Foo
}

func main() {
	fmt.Printf("the answer at %v is %v\n", time.Now(), typedAnswer)
	fmt.Printf("%d squared is %d\n", 5, square(5))
	fmt.Printf("%d + %d is %d\n", 3, 6, sum(3, 6))
	fmt.Printf("printing a pair: ")
	fmt.Println(pair(4))

	x := 7
	y := 8
	x = 9

	fmt.Printf("x = %d, y = %d\n", x, y)
	xs, ys := swap(x, y)
	fmt.Printf("swapped x and y: x = %d, y = %d\n", xs, ys)

	fmt.Printf("keyed struct literal: %#v\n", Foo{X: 42, Y: "test1"})
	fmt.Printf("unkeyed struct literal: %#v\n", Foo{23, "test2"})
	fmt.Printf("address of struct literal: %#v\n", &Foo{X: 22})

	f := Foo{X: 1, Y: "test3"}
	fmt.Printf("method call: %s\n", f.Bar())

	z, t, u := 54, 55, 56
	fmt.Printf("local swap: %d %d %d => ", z, t, u)
	z, t, u = t, u, z
	fmt.Printf("%d, %d, %d\n", z, t, u)

	b := Baz{Z: 0}
	fmt.Printf("before SetZ(%d): %#v\n", 42, b)
	b.SetZ(42)
	fmt.Printf("after SetZ(%d): %#v\n", 42, b)

	q := &Quux{Q: "it works"}
	fmt.Printf("value call on pointer receiver: %s\n", q.Whatever())
	
	m := MultiLevel{F: Foo{X: 42}}
	fmt.Printf("multilevel selector m.F.X: %v\n", m.F.X)
}
