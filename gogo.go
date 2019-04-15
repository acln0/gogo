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
	"go/ast"
	"go/parser"
	"go/token"
	"reflect"
)

// Exec executes the Go code specified by src.
func Exec(src string) error {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "gogosrc", src, 0)
	if err != nil {
		return err
	}

	var mainfunc *ast.FuncDecl
findmain:
	for _, decl := range f.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			if d.Name.Name == "main" {
				mainfunc = d
				break findmain
			}
		}
	}
	if mainfunc == nil {
		return errors.New("no main function")
	}

	execFunc(mainfunc)

	return nil
}

func execFunc(f *ast.FuncDecl) {
	for _, stmt := range f.Body.List {
		execStmt(stmt)
	}
}

func execStmt(stmt ast.Stmt) {
	switch s := stmt.(type) {
	case *ast.ExprStmt:
		execExpr(s.X)
	}
}

func execExpr(expr ast.Expr) []reflect.Value {
	switch e := expr.(type) {
	case *ast.CallExpr:
		return execCallExpr(e)
	}
	panicf("don't know how to handle %T", expr)
	return nil // unreachable
}

func execCallExpr(expr *ast.CallExpr) []reflect.Value {
	var (
		fn   reflect.Value
		args []reflect.Value
	)

	switch fexpr := expr.Fun.(type) {
	case *ast.SelectorExpr:
		switch x := fexpr.X.(type) {
		case *ast.Ident:
			if x.Obj == nil {
				// stdlib package
				fn = stdlib[x.Name].Func[fexpr.Sel.Name]
			}
		default:
			panicf("don't know how to handle %T", fexpr.X)
		}
	}

	for _, arg := range expr.Args {
		args = append(args, execExpr(arg)[0])
	}

	return fn.Call(args)
}

// pkg represents a Go package
type pkg struct {
	// Func maps package-level functions
	Func map[string]reflect.Value
}

func panicf(format string, args ...interface{}) {
	panic(fmt.Sprintf(format, args...))
}
