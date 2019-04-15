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
	"go/constant"
	"go/parser"
	"go/token"
	"reflect"
	"strconv"
	"strings"
)

// Exec executes the Go code specified by src.
func Exec(src string) error {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "gogosrc", src, 0)
	if err != nil {
		return err
	}

	sc := &scope{
		std:    stdlib,
		values: make(map[string]reflect.Value),
		consts: make(map[string]constant.Value),
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
		case *ast.GenDecl:
			sc.evalDecl(d)
		}
	}
	if mainfunc == nil {
		return errors.New("no main function")
	}

	sc.main(mainfunc)

	return nil
}

// scope represents a scope.
type scope struct {
	// std holds standard library packages
	std map[string]pkg

	// value maps identifiers to runtime values
	values map[string]reflect.Value

	// const maps identifiers to constants
	consts map[string]constant.Value
}

// main evaluates the main function.
func (sc *scope) main(f *ast.FuncDecl) {
	for _, stmt := range f.Body.List {
		sc.eval(stmt)
	}
}

// eval evaluates a statement.
func (sc *scope) eval(stmt ast.Stmt) {
	switch s := stmt.(type) {
	case *ast.ExprStmt:
		sc.evalExpr(s.X)
	}
}

// evalExpr evaluates an expression.
func (sc *scope) evalExpr(expr ast.Expr) []reflect.Value {
	switch e := expr.(type) {
	case *ast.CallExpr:
		return sc.evalCallExpr(e)
	case *ast.Ident:
		return []reflect.Value{sc.evalIdent(e)}
	case *ast.BasicLit:
		return []reflect.Value{sc.evalBasicLit(e)}
	}
	panicf("cannot handle %T expression\n", expr)
	return nil // unreachable
}

// evalCallExpr evaluates a call expression.
func (sc *scope) evalCallExpr(call *ast.CallExpr) []reflect.Value {
	var (
		fn   reflect.Value
		args []reflect.Value
	)

	switch fexpr := call.Fun.(type) {
	case *ast.SelectorExpr:
		switch x := fexpr.X.(type) {
		case *ast.Ident:
			if x.Obj == nil {
				// stdlib package
				fn = sc.std[x.Name].Func[fexpr.Sel.Name]
			}
		default:
			panicf("don't know how to handle %T", fexpr.X)
		}
	}

	for _, arg := range call.Args {
		args = append(args, sc.evalExpr(arg)[0])
	}

	return fn.Call(args)
}

// evalIdent evaluates an identifier.
func (sc *scope) evalIdent(ident *ast.Ident) reflect.Value {
	if v, ok := sc.values[ident.Name]; ok {
		return v
	}

	if v, ok := sc.consts[ident.Name]; ok {
		switch v.Kind() {
		case constant.Bool:
			return reflect.ValueOf(constant.BoolVal(v))
		case constant.String:
			return reflect.ValueOf(constant.StringVal(v))
		case constant.Int:
			val, _ := constant.Int64Val(v)
			return reflect.ValueOf(val)
		default:
			panicf("cannot handle %v constant", v.String())
		}
	}

	panicf("value for identifier %s not found", ident.Name)
	return reflect.Value{} // unreachable
}

// evalBasicLit evaluates a basic literal.
func (sc *scope) evalBasicLit(lit *ast.BasicLit) reflect.Value {
	switch lit.Kind {
	case token.INT:
		val, _ := strconv.Atoi(lit.Value)
		return reflect.ValueOf(val)
	case token.STRING:
		val, _ := strconv.Unquote(lit.Value)
		return reflect.ValueOf(val)
	default:
		panicf("cannot evalue %v basic literal", lit.Kind)
		return reflect.Value{} // unreachable
	}
}

// evalDecl evaluates a declaration.
func (sc *scope) evalDecl(gd *ast.GenDecl) {
	switch gd.Tok {
	case token.CONST:
		sc.evalConst(gd)
	case token.IMPORT:
		sc.evalImport(gd)
	default:
		panicf("cannot handle %v declaration", gd.Tok)
	}
}

// evalConst evaluates a constant declaration.
func (sc *scope) evalConst(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		sc.evalConstSpec(spec.(*ast.ValueSpec))
	}
}

// evalConstSpec evaluates a ValueSpec representing a constant declaration.
func (sc *scope) evalConstSpec(vspec *ast.ValueSpec) {
	if vspec.Type != nil {
		panicf("cannot handle typed consts")
	}
	for idx, name := range vspec.Names {
		vexpr := vspec.Values[idx]
		switch ve := vexpr.(type) {
		case *ast.BasicLit:
			cval := constant.MakeFromLiteral(ve.Value, ve.Kind, 0)
			sc.addConst(name.Name, cval)
		default:
			panicf("cannot handle %T constant expressions", vexpr)
		}
	}
}

// evalImport evaluates an import declaration.
func (sc *scope) evalImport(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		sc.evalImportSpec(spec.(*ast.ImportSpec))
	}
}

// evalImportSpec evaluates an import spec. Only standard library imports
// are supported.
func (sc *scope) evalImportSpec(i *ast.ImportSpec) {
	path := strings.Trim(i.Path.Value, `"`)
	stdpkg, ok := stdlib[path]
	if !ok {
		panicf("non-stdlib import path %s", path)
	}

	sc.std[path] = stdpkg
}

// addValue adds a value to the scope.
func (sc *scope) addValue(name string, val reflect.Value) {
	sc.values[name] = val
}

// removeValue removes a value from the scope.
func (sc *scope) removeValue(name string) {
	delete(sc.values, name)
}

// addConst adds a constant to the scope.
func (sc *scope) addConst(name string, val constant.Value) {
	sc.consts[name] = val
}

// removeConst removes a constant from the scope.
func (sc *scope) removeConst(name string) {
	delete(sc.consts, name)
}

func panicf(format string, args ...interface{}) {
	panic(fmt.Sprintf(format, args...))
}
