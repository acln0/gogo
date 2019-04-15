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
	"go/ast"
	"reflect"
)

var builtinType = map[string]reflect.Type{
	"bool":       reflect.TypeOf(true),
	"byte":       reflect.TypeOf(byte(0)),
	"complex128": reflect.TypeOf(complex(float64(0), float64(0))),
	"complex64":  reflect.TypeOf(complex(float32(0), float32(0))),
	"error":      reflect.TypeOf((error)(nil)), // TODO(acln): fix
	"float32":    reflect.TypeOf(float32(0)),
	"float64":    reflect.TypeOf(float64(0)),
	"int":        reflect.TypeOf(int(0)),
	"int16":      reflect.TypeOf(int16(0)),
	"int32":      reflect.TypeOf(int32(0)),
	"int64":      reflect.TypeOf(int64(0)),
	"int8":       reflect.TypeOf(int8(0)),
	"rune":       reflect.TypeOf(rune(0)),
	"string":     reflect.TypeOf(""),
	"uint":       reflect.TypeOf(uint(0)),
	"uint16":     reflect.TypeOf(uint16(0)),
	"uint32":     reflect.TypeOf(uint32(0)),
	"uint64":     reflect.TypeOf(uint64(0)),
	"uint8":      reflect.TypeOf(uint8(0)),
	"uintptr":    reflect.TypeOf(uintptr(0)),
}

func (sc *scope) fieldType(f *ast.Field) reflect.Type {
	switch texp := f.Type.(type) {
	case *ast.Ident:
		return sc.namedType(texp.Name)
	case *ast.ArrayType:
		return sc.arrayType(texp)
	case *ast.StructType:
		return sc.structType(texp)
	default:
		panicf("cannot handle field of type %T", f.Type)
		return nil
	}
}

func (sc *scope) namedType(name string) reflect.Type {
	if named, ok := sc.types[name]; ok {
		return named
	}
	if builtin, ok := builtinType[name]; ok {
		return builtin
	}
	panicf("unknown named type %s", name)
	return nil // unreachable
}

func (sc *scope) arrayType(at *ast.ArrayType) reflect.Type {
	size := int(sc.evalExpr(at.Len)[0].Int())

	var etype reflect.Type
	switch texp := at.Elt.(type) {
	case *ast.Ident:
		etype = sc.namedType(texp.Name)
	default:
		panicf("cannot handle array element type %T", at.Elt)
	}

	return reflect.ArrayOf(size, etype)
}

func (sc *scope) structType(st *ast.StructType) reflect.Type {
	panicf("cannot handle struct types")
	return nil // unreachable
}