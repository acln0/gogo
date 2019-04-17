package main

import (
	"fmt"
	"time"
)

func packageLevelSum(x, y int) int {
	return x + y
}

const (
	alsoTheAnswer = answer
	answer        = 42
)

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

func basics() {
	type answerT int

	const (
		typedAnswer answerT = alsoTheAnswer
	)

	swap := func(x, y int) (int, int) {
		return y, x
	}

	sum := func(x, y int) int {
		return x + y
	}

	square := func(x int) int {
		return x * x
	}

	pair := func(z int) (int, int) {
		return z, z
	}

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

	type MultiLevel struct {
		F Foo
	}

	m := MultiLevel{F: Foo{X: 42}}
	fmt.Printf("multilevel selector m.F.X: %v\n", m.F.X)
}

func methods() {
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
}

func maps() {
	m := make(map[string]string)
	m["test"] = "hello"
	fmt.Printf("m[%q] = %q\n", "test", m["test"])

	val := m["bogus"]
	fmt.Printf("m[%q] = %q\n", "bogus", val)

	val, ok := m["bogus"]
	fmt.Printf("m[%q] = %q, %t\n", "bogus", val, ok)

	mcap := make(map[string]string, 2)
	mcap["x"] = "y"
	mcap["z"] = "t"
	fmt.Printf("mcap: map with capacity: %v\n", mcap)

	delete(mcap, "x")
	fmt.Printf("after delete(mcap, %q): %v\n", "x", mcap)
}

func goroutines() {
	ch := make(chan string)
	go func() {
		ch <- "hello"
	}()
	greeting := <-ch
	fmt.Printf("the greeting is %s\n", greeting)

	ch2 := make(chan int)
	close(ch2)
	v, ok := <-ch2
	fmt.Printf("got %d, %t from closed channel\n", v, ok)

	neverreceives := make(chan float64)
	neverclosed := make(chan int)
	select {
	case <-time.After(10 * 1000 * 1000): // TODO(acln): time.Millisecond
		fmt.Println("timeout")
	case v := <-neverclosed:
		fmt.Printf("bogus value %d\n", v)
	case neverreceives <- 42.0:
		fmt.Println("bogus send")
	}
}

func main() {
	fmt.Println("==== package level ====")
	x := 1001
	y := 1002
	fmt.Printf("package level sum: %d + %d = %d\n", x, y, packageLevelSum(x, y))

	hr()

	fmt.Println("==== basics ====")
	basics()
	hr()

	fmt.Println("==== methods ====")
	methods()
	hr()

	fmt.Println("==== maps ====")
	maps()
	hr()

	fmt.Println("==== goroutines ====")
	goroutines()
	hr()
}

func hr() {
	fmt.Println("------------------")
	fmt.Println("")
}
