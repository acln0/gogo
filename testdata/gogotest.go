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

	fmt.Printf("printing a keyed struct literal: %#v\n", Foo{X: 42, Y: "test1"})
	fmt.Printf("printing an unkeyed struct literal: %#v\n", Foo{23, "test2"})
}
