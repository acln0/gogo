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
	"io/ioutil"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestExec(t *testing.T) {
	/*
		t.Run("gogotest", func(t *testing.T) {
			if err := Exec("testdata/gogotest.go"); err != nil {
				t.Fatal(err)
			}
		})
	*/

	gotests, err := ioutil.ReadDir("testdata/gotests")
	if err != nil {
		t.Fatal(err)
	}
	for _, testfile := range gotests {
		name := strings.TrimSuffix(testfile.Name(), ".go")
		t.Run(name, func(t *testing.T) {
			gofile := filepath.Join("testdata/gotests", testfile.Name())
			src, err := os.Open(gofile)
			if err != nil {
				t.Fatal(err)
			}
			defer src.Close()
			interp := &Interpreter{
				Source:   src,
				Filename: gofile,
				Entry:    "main",
			}
			if err := interp.Run(); err != nil {
				t.Fatal(err)
			}
		})
	}
}
