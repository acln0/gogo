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
	"go/ast"
	"go/types"
	"reflect"
	"unsafe"
)

var _ = fmt.Println

var builtinType = map[string]reflect.Type{
	"bool":          reflect.TypeOf(true),
	"byte":          reflect.TypeOf(byte(0)),
	"complex128":    reflect.TypeOf(complex(float64(0), float64(0))),
	"complex64":     reflect.TypeOf(complex(float32(0), float32(0))),
	"error":         reflect.TypeOf((error)(nil)), // TODO(acln): fix
	"float32":       reflect.TypeOf(float32(0)),
	"float64":       reflect.TypeOf(float64(0)),
	"int":           reflect.TypeOf(int(0)),
	"int16":         reflect.TypeOf(int16(0)),
	"int32":         reflect.TypeOf(int32(0)),
	"int64":         reflect.TypeOf(int64(0)),
	"int8":          reflect.TypeOf(int8(0)),
	"rune":          reflect.TypeOf(rune(0)),
	"string":        reflect.TypeOf(""),
	"uint":          reflect.TypeOf(uint(0)),
	"uint16":        reflect.TypeOf(uint16(0)),
	"uint32":        reflect.TypeOf(uint32(0)),
	"uint64":        reflect.TypeOf(uint64(0)),
	"uint8":         reflect.TypeOf(uint8(0)),
	"uintptr":       reflect.TypeOf(uintptr(0)),
	"unsafepointer": reflect.TypeOf(unsafe.Pointer(nil)),
}

var basicKind = map[types.BasicKind]string{
	types.Bool:          "bool",
	types.Int:           "int",
	types.Int8:          "int8",
	types.Int16:         "int16",
	types.Int32:         "int32",
	types.Int64:         "int64",
	types.Uint:          "uint",
	types.Uint8:         "uint8",
	types.Uint16:        "uint16",
	types.Uint32:        "uint32",
	types.Uint64:        "uint64",
	types.Uintptr:       "uintptr",
	types.Float32:       "float32",
	types.Float64:       "float64",
	types.Complex64:     "complex64",
	types.Complex128:    "complex128",
	types.String:        "string",
	types.UnsafePointer: "unsafepointer",
}

func (sc *scope) fieldType(f *ast.Field) reflect.Type {
	switch texp := f.Type.(type) {
	case *ast.Ident:
		return sc.namedType(texp.Name)
	case *ast.ArrayType:
		return sc.arrayType(texp)
	case *ast.StructType:
		return sc.structType(texp)
	}

	sc.err("cannot handle field of type %T", f.Type)
	return nil
}

func (sc *scope) namedType(name string) reflect.Type {
	if named, ok := sc.types[name]; ok {
		return named
	}
	if builtin, ok := builtinType[name]; ok {
		return builtin
	}

	sc.err("unknown named type %s", name)
	return nil // unreachable
}

func (sc *scope) dynamicType(typ types.Type) reflect.Type {
	switch t := typ.(type) {
	case *types.Basic:
		return builtinType[basicKind[t.Kind()]]
	case *types.Struct:
		return sc.dynamicStructType(typ.(*types.Struct))
	case *types.Named:
		return sc.dynamicType(t.Underlying())
	default:
		sc.err("cannot handle dynamic type of %T", typ)
		return nil // unreachable
	}
}

func (sc *scope) dynamicStructType(stype *types.Struct) reflect.Type {
	var fields []reflect.StructField

	for i := 0; i < stype.NumFields(); i++ {
		field := stype.Field(i)
		sf := reflect.StructField{
			Name:      field.Name(),
			Type:      sc.dynamicType(field.Type()),
			Tag:       reflect.StructTag(stype.Tag(i)),
			Anonymous: field.Anonymous(),
		}
		fields = append(fields, sf)
	}

	return reflect.StructOf(fields)
}

func (sc *scope) arrayType(at *ast.ArrayType) reflect.Type {
	size := int(sc.evalExpr(at.Len)[0].Int())

	var etype reflect.Type
	switch texp := at.Elt.(type) {
	case *ast.Ident:
		etype = sc.namedType(texp.Name)
	default:
		sc.err("cannot handle array element type %T", at.Elt)
	}

	return reflect.ArrayOf(size, etype)
}

func (sc *scope) structType(st *ast.StructType) reflect.Type {
	sc.err("cannot handle struct types")
	return nil // unreachable
}
