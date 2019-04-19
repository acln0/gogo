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
	"errors"
	"fmt"
	"os"
	"reflect"
	"time"
)

var stdlib = Runtime{
	"errors": {
		Func: map[string]reflect.Value{
			"New": reflect.ValueOf(errors.New),
		},
	},
	"fmt": {
		Func: map[string]reflect.Value{
			"Print":   reflect.ValueOf(fmt.Print),
			"Println": reflect.ValueOf(fmt.Println),
			"Printf":  reflect.ValueOf(fmt.Printf),
			"Sprintf": reflect.ValueOf(fmt.Sprintf),
		},
	},
	"os": {
		Func: map[string]reflect.Value{
			"Exit": reflect.ValueOf(os.Exit),
		},
	},
	"time": {
		Func: map[string]reflect.Value{
			"After": reflect.ValueOf(time.After),
			"Now":   reflect.ValueOf(time.Now),
			"Sleep": reflect.ValueOf(time.Sleep),
		},
	},
}

// Stdlib returns the standard library runtime.
func Stdlib() Runtime {
	return stdlib
}
