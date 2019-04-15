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
		std:              stdlib,
		values:           make(map[string]reflect.Value),
		consts:           make(map[string]constant.Value),
		unresolvedConsts: make(map[string]string),
		funcs:            make(map[string]reflect.Value),
		methods:          make(map[string]map[string]reflect.Value),
	}

	for _, decl := range f.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			sc.evalFuncDecl(d)
		case *ast.GenDecl:
			sc.evalDecl(d)
		}
	}

	sc.resolveConsts()

	main, ok := sc.funcs["main"]
	if !ok {
		return errors.New("missing main function")
	}

	main.Call(nil)

	return nil
}

// scope represents a scope.
type scope struct {
	// std holds standard library packages
	std map[string]pkg

	// value maps identifiers to runtime values
	values map[string]reflect.Value

	// consts maps identifiers to constants
	consts map[string]constant.Value

	// unresolvedConsts maps identifiers to unresolved const identifiers
	unresolvedConsts map[string]string

	// funcs maps function names to runtime function values
	funcs map[string]reflect.Value

	// methods maps methods to sets of runtime function values
	methods map[string]map[string]reflect.Value

	// types maps type names to runtime types
	types map[string]reflect.Type
}

// eval evaluates a statement.
func (sc *scope) eval(stmt ast.Stmt) []reflect.Value {
	switch s := stmt.(type) {
	case *ast.ExprStmt:
		return sc.evalExpr(s.X)
	case *ast.ReturnStmt:
		return sc.evalReturn(s)
	default:
		panicf("cannot handle %T statement", stmt)
		return nil // unreachable
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
	case *ast.BinaryExpr:
		return []reflect.Value{sc.evalBinaryExpr(e)}
	}
	panicf("cannot handle %T expression\n", expr)
	return nil // unreachable
}

// evalReturn evaluates a return statement.
func (sc *scope) evalReturn(ret *ast.ReturnStmt) []reflect.Value {
	var values []reflect.Value
	for _, res := range ret.Results {
		values = append(values, sc.evalExpr(res)[0])
	}
	return values
}

// evalCallExpr evaluates a call expression.
func (sc *scope) evalCallExpr(call *ast.CallExpr) []reflect.Value {
	var (
		fn   reflect.Value
		args []reflect.Value
	)

	switch fexpr := call.Fun.(type) {
	case *ast.Ident:
		if f, ok := sc.funcs[fexpr.Name]; ok {
			fn = f
		}
	case *ast.SelectorExpr:
		switch x := fexpr.X.(type) {
		case *ast.Ident:
			if x.Obj == nil {
				if f, ok := sc.funcs[x.Name]; ok {
					fn = f
				}
				if f, ok := sc.std[x.Name].Func[fexpr.Sel.Name]; ok {
					// stdlib
					fn = f
				}
			}
		default:
			panicf("cannot handle selector of type %T", fexpr.X)
		}
	default:
		panicf("cannot handle function expression of type %T", call.Fun)
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
		panicf("cannot evaluate %v basic literal", lit.Kind)
		return reflect.Value{} // unreachable
	}
}

// evalBinaryExpr evaluates a binary expression.
func (sc *scope) evalBinaryExpr(be *ast.BinaryExpr) reflect.Value {
	switch be.Op {
	case token.MUL:
		x := sc.evalExpr(be.X)[0]
		y := sc.evalExpr(be.Y)[0]
		if x.Type().ConvertibleTo(builtinType["int64"]) {
			res := reflect.New(x.Type())
			res.Elem().SetInt(sc.evalIntMul(x, y).Int())
			return res.Elem()
		}
	}
	panicf("cannot evaluate binary expression of type %v", be.Op)
	return reflect.Value{} // unreachable
}

// evalIntMul evaluates x * y, where x and y are convertible to integers.
func (sc *scope) evalIntMul(x, y reflect.Value) reflect.Value {
	return reflect.ValueOf(x.Int() * y.Int())
}

// evalFuncDecl evaluates a function declaration.
func (sc *scope) evalFuncDecl(fd *ast.FuncDecl) {
	var (
		recvfield *ast.Field   // receiver, if any
		fparams   []*ast.Field // formal parameters, if any
		fresults  []*ast.Field // formal results, if any
	)
	if fd.Recv != nil {
		recvfield = fd.Recv.List[0]
	}
	if fd.Type.Params != nil {
		fparams = fd.Type.Params.List
	}
	if fd.Type.Results != nil {
		fresults = fd.Type.Results.List
	}

	fn := func(params []reflect.Value) []reflect.Value {
		if recvfield != nil {
			name := recvfield.Names[0].Name
			sc.addValue(name, params[0])
			defer sc.removeValue(name)
			params = params[1:]
		}
		for idx, fparam := range fparams {
			name := fparam.Names[0].Name
			sc.addValue(name, params[idx])
			defer sc.removeValue(name)
		}
		for _, fresult := range fresults {
			if len(fresult.Names) != 0 {
				panic("cannot handle named returns")
			}
		}
		for _, stmt := range fd.Body.List {
			_, isReturn := stmt.(*ast.ReturnStmt)
			values := sc.eval(stmt)
			if isReturn {
				return values
			}
		}
		// no return statement
		return nil
	}

	var (
		argtypes    []reflect.Type
		returntypes []reflect.Type
	)

	if recvfield != nil {
		argtypes = append(argtypes, sc.fieldType(recvfield))
	}
	for _, field := range fparams {
		argtypes = append(argtypes, sc.fieldType(field))
	}
	for _, field := range fresults {
		returntypes = append(returntypes, sc.fieldType(field))
	}

	variadic := false // TODO(acln): fix
	ftype := reflect.FuncOf(argtypes, returntypes, variadic)

	sc.funcs[fd.Name.Name] = reflect.MakeFunc(ftype, fn)
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
		case *ast.Ident:
			sc.unresolvedConsts[name.Name] = ve.Name
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

// resolveConsts resolves all unresolved constants.
func (sc *scope) resolveConsts() {
	for name, dep := range sc.unresolvedConsts {
		for {
			cval, resolved := sc.consts[dep]
			if !resolved {
				dep = sc.unresolvedConsts[dep]
				continue
			} else {
				sc.addConst(name, cval)
				delete(sc.unresolvedConsts, name)
				break
			}
		}
	}
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
