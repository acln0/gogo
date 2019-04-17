package main

import (
	"fmt"
	"time"
)

const (
	alsoTheAnswer = answer
	answer        = 42
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

func main() {
	fmt.Printf("the answer at %v is %v\n", time.Now(), alsoTheAnswer)
	fmt.Printf("%d squared is %d\n", 5, square(5))
	fmt.Printf("%d + %d is %d\n", 3, 6, sum(3, 6))

	x := 7
	y := 8
	x = 9

	fmt.Printf("x = %d, y = %d\n", x, y)
	xs, ys := swap(x, y)
	fmt.Printf("swapped x and y: x = %d, y = %d\n", xs, ys)
}
