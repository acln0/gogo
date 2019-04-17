// Copyright 2019 Andrei Tudor Călin
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
// ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
// ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
// OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

package gogo

import (
	"fmt"
	"reflect"
	"time"
)

// pkg represents a Go package
type pkg struct {
	// Func maps package-level functions
	Func map[string]reflect.Value
}

var stdlib = map[string]pkg{
	"fmt": {
		Func: map[string]reflect.Value{
			"Println": reflect.ValueOf(fmt.Println),
			"Printf":  reflect.ValueOf(fmt.Printf),
			"Sprintf": reflect.ValueOf(fmt.Sprintf),
		},
	},
	"time": {
		Func: map[string]reflect.Value{
			"Now": reflect.ValueOf(time.Now),
		},
	},
}
