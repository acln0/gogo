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
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"reflect"
	"runtime"
	"strconv"
	"strings"
)

// Exec executes the Go source file specified by srcfile.
func Exec(srcfile string) (err error) {
	fset := token.NewFileSet()
	src, err := os.Open(srcfile)
	if err != nil {
		return err
	}
	f, err := parser.ParseFile(fset, srcfile, src, 0)
	if err != nil {
		return err
	}

	typecfg := &types.Config{
		Importer: importer.ForCompiler(fset, "gc", nil),
		Error:    func(err error) { fmt.Println(err) },
	}
	info := &types.Info{
		Types:      make(map[ast.Expr]types.TypeAndValue),
		Defs:       make(map[*ast.Ident]types.Object),
		Implicits:  make(map[ast.Node]types.Object),
		Selections: make(map[*ast.SelectorExpr]*types.Selection),
		Scopes:     make(map[ast.Node]*types.Scope),
	}
	p, err := typecfg.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		return err
	}
	_ = p

	sc := &scope{
		std:              stdlib,
		values:           make(map[string]reflect.Value),
		consts:           make(map[string]constant.Value),
		unresolvedConsts: make(map[string]string),
		funcs:            make(map[string]reflect.Value),
		methods:          make(map[string]map[string]reflect.Value),
	}

	defer func() {
		if r := recover(); r != nil {
			e, ok := r.(error)
			if !ok {
				panic(r)
			}
			if _, rok := e.(runtime.Error); rok {
				panic(r)
			}
			err = e
		}
	}()

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
	// parent is the parent scope, or nil if the scope represents the
	// top-level package scope.
	parent *scope

	// std holds standard library packages.
	std map[string]pkg

	// value maps identifiers to runtime values.
	values map[string]reflect.Value

	// consts maps identifiers to constants.
	consts map[string]constant.Value

	// unresolvedConsts maps identifiers to unresolved const identifiers.
	unresolvedConsts map[string]string

	// funcs maps function names to runtime function values.
	funcs map[string]reflect.Value

	// methods maps methods to sets of runtime function values.
	methods map[string]map[string]reflect.Value

	// types maps type names to runtime types.
	types map[string]reflect.Type
}

// eval evaluates a statement.
func (sc *scope) eval(stmt ast.Stmt) []reflect.Value {
	switch s := stmt.(type) {
	case *ast.ExprStmt:
		return sc.evalExpr(s.X)
	case *ast.ReturnStmt:
		return sc.evalReturn(s)
	case *ast.AssignStmt:
		sc.evalAssign(s)
		return nil
	default:
		sc.err("cannot handle %T statement", stmt)
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
	sc.err("cannot handle %T expression", expr)
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

// evalAssign evaluates an assignment statement.
func (sc *scope) evalAssign(a *ast.AssignStmt) {
	var values []reflect.Value
	for _, rhsexpr := range a.Rhs {
		values = append(values, sc.evalExpr(rhsexpr)...)
	}

	for idx, lhsexpr := range a.Lhs {
		switch ident := lhsexpr.(type) {
		case *ast.Ident:
			switch a.Tok {
			case token.DEFINE:
				v, ok := sc.lookup(ident.Name)
				if ok {
					v.Set(values[idx])
				} else {
					sc.values[ident.Name] = values[idx]
				}
			case token.ASSIGN:
				v, _ := sc.lookup(ident.Name)
				v.Set(values[idx])
			default:
				sc.err("cannot handle %v token in assignment", a.Tok)
			}
		default:
			sc.err("cannot handle %T expression in assignment", lhsexpr)
		}
	}
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
			sc.err("cannot handle selector of type %T", fexpr.X)
		}
	default:
		sc.err("cannot handle function expression of type %T", call.Fun)
	}

	for _, arg := range call.Args {
		args = append(args, sc.evalExpr(arg)[0])
	}

	return fn.Call(args)
}

// evalIdent evaluates an identifier.
func (sc *scope) evalIdent(ident *ast.Ident) reflect.Value {
	if v, ok := sc.lookup(ident.Name); ok {
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
			sc.err("cannot handle %v constant", v.String())
		}
	}

	sc.err("value for identifier %s not found", ident.Name)
	return reflect.Value{} // unreachable
}

// evalBasicLit evaluates a basic literal.
func (sc *scope) evalBasicLit(lit *ast.BasicLit) reflect.Value {
	switch lit.Kind {
	case token.INT:
		val, _ := strconv.Atoi(lit.Value)
		res := reflect.New(reflect.TypeOf(int(0)))
		res.Elem().Set(reflect.ValueOf(val))
		return res.Elem()
	case token.STRING:
		val, _ := strconv.Unquote(lit.Value)
		res := reflect.New(reflect.TypeOf(""))
		res.Elem().Set(reflect.ValueOf(val))
		return res.Elem()
	}

	sc.err("cannot evaluate %v basic literal", lit.Kind)
	return reflect.Value{} // unreachable
}

// evalBinaryExpr evaluates a binary expression.
func (sc *scope) evalBinaryExpr(be *ast.BinaryExpr) reflect.Value {
	switch be.Op {
	case token.ADD:
		x := sc.evalExpr(be.X)[0]
		y := sc.evalExpr(be.Y)[0]
		if x.Type().ConvertibleTo(builtinType["int64"]) {
			res := reflect.New(x.Type())
			res.Elem().SetInt(sc.evalIntAdd(x, y).Int())
			return res.Elem()
		}
	case token.MUL:
		x := sc.evalExpr(be.X)[0]
		y := sc.evalExpr(be.Y)[0]
		if x.Type().ConvertibleTo(builtinType["int64"]) {
			res := reflect.New(x.Type())
			res.Elem().SetInt(sc.evalIntMul(x, y).Int())
			return res.Elem()
		}
	}

	sc.err("cannot evaluate binary expression of type %v", be.Op)
	return reflect.Value{} // unreachable
}

// evalIntAdd evaluates x + y, where x and y are integers.
func (sc *scope) evalIntAdd(x, y reflect.Value) reflect.Value {
	return reflect.ValueOf(x.Int() + y.Int())
}

// evalIntMul evaluates x * y, where x and y are integers.
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
			sc.values[name] = params[0]
			defer delete(sc.values, name)
			params = params[1:]
		}
		idx := 0
		for _, fparam := range fparams {
			for _, ident := range fparam.Names {
				name := ident.Name
				sc.values[name] = params[idx]
				defer delete(sc.values, name)
				idx++
			}
		}
		for _, fresult := range fresults {
			if len(fresult.Names) != 0 {
				sc.err("cannot handle named returns")
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
		for range field.Names {
			argtypes = append(argtypes, sc.fieldType(field))
		}
	}
	for _, field := range fresults {
		if len(field.Names) > 0 {
			for range field.Names {
				returntypes = append(returntypes, sc.fieldType(field))
			}
		} else {
			returntypes = append(returntypes, sc.fieldType(field))
		}
	}

	variadic := false // TODO(acln): fix
	ftype := reflect.FuncOf(argtypes, returntypes, variadic)

	sc.funcs[fd.Name.Name] = reflect.MakeFunc(ftype, fn)
}

// evalDecl evaluates a declaration.
func (sc *scope) evalDecl(gd *ast.GenDecl) {
	switch gd.Tok {
	case token.CONST:
		sc.evalConstDecl(gd)
	case token.VAR:
		sc.evalVarDecl(gd)
	case token.IMPORT:
		sc.evalImportDecl(gd)
	case token.TYPE:
		sc.evalTypeDecl(gd)
	default:
		sc.err("unreachable: %v GenDecl type", gd.Tok)
	}
}

// evalConstDecl evaluates a constant declaration.
func (sc *scope) evalConstDecl(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		sc.evalConstSpec(spec.(*ast.ValueSpec))
	}
}

// evalConstSpec evaluates a ValueSpec representing a constant declaration.
func (sc *scope) evalConstSpec(vspec *ast.ValueSpec) {
	if vspec.Type != nil {
		sc.err("cannot handle typed consts")
	}
	for idx, name := range vspec.Names {
		vexpr := vspec.Values[idx]
		switch ve := vexpr.(type) {
		case *ast.BasicLit:
			cval := constant.MakeFromLiteral(ve.Value, ve.Kind, 0)
			sc.consts[name.Name] = cval
		case *ast.Ident:
			sc.unresolvedConsts[name.Name] = ve.Name
		default:
			sc.err("cannot handle %T constant expressions", vexpr)
		}
	}
}

// evalVarDecl evaluates a variable declaration.
func (sc *scope) evalVarDecl(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		sc.evalVarSpec(spec.(*ast.ValueSpec))
	}
}

// evalVarSpec evaluates a ValueSpec representing a variable declaration.
func (sc *scope) evalVarSpec(vspec *ast.ValueSpec) {
	sc.err("cannot evaluate variable spec")
}

// evalImportDecl evaluates an import declaration.
func (sc *scope) evalImportDecl(gd *ast.GenDecl) {
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
		sc.err("non-stdlib import path %s", path)
	}

	sc.std[path] = stdpkg
}

// evalTypeDecl evaluates a type declaration.
func (sc *scope) evalTypeDecl(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		sc.evalTypeSpec(spec.(*ast.TypeSpec))
	}
}

// evalTypeSpec evaluates a type spec.
func (sc *scope) evalTypeSpec(ts *ast.TypeSpec) {
	sc.err("cannot evaluate type spec")
}

// lookup looks up a value. It starts from the current scope, and walks
// the parent scopes if necessary. It returns a reflect.Value v such that
// v.CanSet() == true. Returns reflect.Value{}, false if no such value exists.
func (sc *scope) lookup(name string) (reflect.Value, bool) {
	curr := sc
	for curr != nil {
		v, ok := curr.values[name]
		if ok {
			return v, true
		}
		curr = curr.parent
	}
	return reflect.Value{}, false
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
				sc.consts[name] = cval
				delete(sc.unresolvedConsts, name)
				break
			}
		}
	}
}

func (sc *scope) err(format string, args ...interface{}) {
	panic(fmt.Errorf(format, args...))
}
