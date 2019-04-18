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
	"strconv"
	"strings"
	"unsafe"
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
	pkg, err := typecfg.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		return err
	}

	pkgscope := newScope(nil)
	pkgscope.typeinfo = info
	pkgscope.pkg = pkg

	/*
		defer func() {
			if r := recover(); r != nil {
				e, ok := r.(error)
				if !ok {
					panic(r)
				}
				if _, interp := e.(interpreterError); !interp {
					panic(r)
				}
				err = e
			}
		}()
	*/

	for _, decl := range f.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			pkgscope.evalFuncDecl(d.Recv, d.Name, d.Type, d.Body)
		case *ast.GenDecl:
			pkgscope.evalGenDecl(d)
		}
	}

	main, ok := pkgscope.funcs["main"]
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

	// valuetypes maps identifiers referring to values to their
	// respective types.
	valuetypes map[string]types.Type

	// consts maps identifiers to constants.
	consts map[string]types.TypeAndValue

	// funcs maps function names to runtime function values.
	funcs map[string]reflect.Value

	// methods maps methods to sets of runtime function values.
	methods map[string]map[string]reflect.Value

	// types maps type names to runtime types.
	types map[string]reflect.Type

	// typeinfo holds type information.
	typeinfo *types.Info

	// pkg holds the type checked package.
	pkg *types.Package
}

func newScope(parent *scope) *scope {
	sc := &scope{
		parent:     parent,
		std:        stdlib,
		values:     make(map[string]reflect.Value),
		valuetypes: make(map[string]types.Type),
		consts:     make(map[string]types.TypeAndValue),
		funcs:      make(map[string]reflect.Value),
		methods:    make(map[string]map[string]reflect.Value),
		types:      make(map[string]reflect.Type),
	}
	if parent != nil {
		sc.typeinfo = parent.typeinfo
		sc.pkg = parent.pkg
	}
	return sc
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
	case *ast.DeclStmt:
		return sc.evalDecl(s)
	case *ast.GoStmt:
		sc.evalGo(s)
		return nil
	case *ast.SendStmt:
		sc.evalSend(s)
		return nil
	case *ast.SelectStmt:
		sc.evalSelect(s)
		return nil
	case *ast.IfStmt:
		sc.evalIf(s)
		return nil
	case *ast.ForStmt:
		sc.evalFor(s)
		return nil
	case *ast.IncDecStmt:
		sc.evalIncDec(s)
		return nil
	case *ast.SwitchStmt:
		sc.evalSwitch(s)
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
	case *ast.UnaryExpr:
		return sc.evalUnaryExpr(e, false)
	case *ast.BinaryExpr:
		return []reflect.Value{sc.evalBinaryExpr(e)}
	case *ast.CompositeLit:
		return []reflect.Value{sc.evalCompositeLit(e)}
	case *ast.KeyValueExpr:
		return sc.evalExpr(e.Value)
	case *ast.SelectorExpr:
		return sc.evalSelectorExpr(e)
	case *ast.FuncLit:
		return []reflect.Value{sc.evalFuncLit(e)}
	case *ast.IndexExpr:
		return sc.evalIndexExpr(e, zeroval, false)
	case *ast.SliceExpr:
		return []reflect.Value{sc.evalSliceExpr(e)}
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

func copyval(val reflect.Value) reflect.Value {
	newval := reflect.New(val.Type())
	newval.Elem().Set(val)
	return newval.Elem()
}

// evalAssign evaluates an assignment statement.
func (sc *scope) evalAssign(a *ast.AssignStmt) {
	var (
		values     []reflect.Value
		valuetypes []types.Type
	)
	for _, rhsexpr := range a.Rhs {
		var rhsvalues []reflect.Value

		iexpr, isIndexExpr := rhsexpr.(*ast.IndexExpr)
		if isIndexExpr && len(a.Lhs) > len(a.Rhs) {
			// v, ok := m[k]
			rhsvalues = sc.evalIndexExpr(iexpr, zeroval, true)
		}

		uexpr, isUnaryExpr := rhsexpr.(*ast.UnaryExpr)
		if isUnaryExpr && uexpr.Op == token.ARROW && len(a.Lhs) > len(a.Rhs) {
			// v, ok := <-ch
			rhsvalues = sc.evalUnaryExpr(uexpr, true)
		}

		if rhsvalues == nil {
			rhsvalues = sc.evalExpr(rhsexpr)
		}

		for _, v := range rhsvalues {
			values = append(values, v)

			var vtype types.Type
			tt, ok := sc.typeinfo.Types[rhsexpr]
			if ok {
				vtype = tt.Type
			}
			valuetypes = append(valuetypes, vtype)
		}
	}

	for i := 0; i < len(values); i++ {
		values[i] = copyval(values[i]) // don't break on x, y = y, x
	}

	for idx, lexpr := range a.Lhs {
		switch expr := lexpr.(type) {
		case *ast.Ident:
			switch a.Tok {
			case token.DEFINE:
				v, ok := sc.lookupValue(expr.Name)
				if ok {
					v.Set(values[idx])
				} else {
					sc.values[expr.Name] = values[idx]
					sc.valuetypes[expr.Name] = valuetypes[idx]
				}
			case token.ASSIGN:
				v, _ := sc.lookupValue(expr.Name)
				v.Set(values[idx])
			default:
				sc.err("cannot handle %v token in assignment", a.Tok)
			}
		case *ast.SelectorExpr:
			val := sc.evalExpr(lexpr)[0]
			val.Set(values[idx])
		case *ast.IndexExpr:
			sc.evalIndexExpr(expr, values[idx], false)
		default:
			sc.err("cannot handle %T expression in assignment", lexpr)
		}
	}
}

// evalAssignRecv evaluates an assignment statement after a chosen receive
// in a select statement.
func (sc *scope) evalAssignRecv(as *ast.AssignStmt, val reflect.Value, ok bool) {
	for i, lexpr := range as.Lhs {
		var rhsval reflect.Value
		if i == 0 {
			rhsval = val
		} else {
			rhsval = reflect.ValueOf(ok)
		}
		switch expr := lexpr.(type) {
		case *ast.Ident:
			switch as.Tok {
			case token.DEFINE:
				v, ok := sc.lookupValue(expr.Name)
				if ok {
					v.Set(rhsval)
				} else {
					sc.values[expr.Name] = rhsval
					rexpr := as.Rhs[0].(*ast.UnaryExpr).X
					rtype := sc.typeinfo.Types[rexpr].Type
					sc.valuetypes[expr.Name] = rtype
				}
			case token.ASSIGN:
				v, _ := sc.lookupValue(expr.Name)
				v.Set(rhsval)
			default:
				sc.err("cannot handle %v token in assignment", as.Tok)
			}
		case *ast.SelectorExpr:
			val := sc.evalExpr(lexpr)[0]
			val.Set(rhsval)
		case *ast.IndexExpr:
			sc.evalIndexExpr(expr, rhsval, false)
		default:
			sc.err("cannot handle %T expression in receive assignment", lexpr)
		}
	}
}

// evalDecl evaluates a declaration.
func (sc *scope) evalDecl(ds *ast.DeclStmt) []reflect.Value {
	sc.evalGenDecl(ds.Decl.(*ast.GenDecl))
	return nil
}

// evalGo evaluates a go statement.
func (sc *scope) evalGo(gs *ast.GoStmt) {
	child := sc.enter("")
	go child.evalCallExpr(gs.Call)
}

// evalSend evaluates a send statement.
func (sc *scope) evalSend(ss *ast.SendStmt) {
	chanv := sc.evalExpr(ss.Chan)[0]
	val := sc.evalExpr(ss.Value)[0]
	chanv.Send(val)
}

// evalSelect evaluates a select statement.
func (sc *scope) evalSelect(ss *ast.SelectStmt) {
	var (
		cases  []reflect.SelectCase
		blocks [][]ast.Stmt
	)

	onrecv := map[int]func(*scope, reflect.Value, bool){}

	for index, blockstmt := range ss.Body.List {
		var (
			dir   reflect.SelectDir
			chanv reflect.Value
			sendv reflect.Value
		)

		commclause := blockstmt.(*ast.CommClause)

		switch commstmt := commclause.Comm.(type) {
		case *ast.ExprStmt:
			// <-ch
			switch expr := commstmt.X.(type) {
			case *ast.UnaryExpr:
				switch expr.Op {
				case token.ARROW:
					dir = reflect.SelectRecv
					chanv = sc.evalExpr(expr.X)[0]
				default:
					sc.err("bogus unary op %v in expression statement in select", expr.Op)
				}
			default:
				sc.err("bogus %T expression in select", commstmt)
			}
		case *ast.AssignStmt:
			// v := <-ch or v, ok := <-ch or v, ok = ch
			rhs := commstmt.Rhs[0]
			switch expr := rhs.(type) {
			case *ast.UnaryExpr:
				switch expr.Op {
				case token.ARROW:
					dir = reflect.SelectRecv
					chanv = sc.evalExpr(expr.X)[0]
				default:
					sc.err("bogus unary op %v in expression statement in select", expr.Op)
				}
			default:
				sc.err("bogus %T expression in select", commstmt)
			}
			onrecv[index] = func(childsc *scope, val reflect.Value, ok bool) {
				childsc.evalAssignRecv(commstmt, val, ok)
			}
		case *ast.SendStmt:
			// ch <- val
			dir = reflect.SelectSend
			chanv = sc.evalExpr(commstmt.Chan)[0]
			sendv = sc.evalExpr(commstmt.Value)[0]
		}

		cases = append(cases, reflect.SelectCase{
			Dir:  dir,
			Chan: chanv,
			Send: sendv,
		})
		blocks = append(blocks, commclause.Body)
	}

	chosen, res, ok := reflect.Select(cases)

	for _, stmt := range blocks[chosen] {
		child := sc.enter("")
		if fn := onrecv[chosen]; fn != nil {
			fn(child, res, ok)
		}
		child.eval(stmt)
	}
}

// evalIf evaluates an if statement.
func (sc *scope) evalIf(is *ast.IfStmt) {
	sc = sc.enter("")
	if is.Init != nil {
		sc.eval(is.Init)
	}
	cond := sc.evalExpr(is.Cond)[0].Bool()
	if cond {
		for _, stmt := range is.Body.List {
			sc.eval(stmt)
		}
	} else {
		if is.Else != nil {
			for _, stmt := range is.Else.(*ast.BlockStmt).List {
				sc.eval(stmt)
			}
		}
	}
}

// evalFor evaluates a for statement.
func (sc *scope) evalFor(fs *ast.ForStmt) {
	sc = sc.enter("")
	if fs.Init != nil {
		sc.eval(fs.Init)
	}
	for {
		if fs.Cond != nil {
			cond := sc.evalExpr(fs.Cond)[0].Bool()
			if !cond {
				return
			}
		}

		for _, stmt := range fs.Body.List {
			sc.eval(stmt)
		}

		if fs.Post != nil {
			sc.eval(fs.Post)
		}
	}
}

// evalIncDec evaluates ++ or --
func (sc *scope) evalIncDec(ids *ast.IncDecStmt) {
	var delta int64

	switch ids.Tok {
	case token.INC:
		delta = 1
	case token.DEC:
		delta = -1
	default:
		sc.err("bogus token %v in IncDec statament", ids.Tok)
	}

	val := sc.evalExpr(ids.X)[0]
	val.Set(reflect.ValueOf(val.Int() + delta).Convert(val.Type()))
}

// evalSwitch evaluates a switch statement.
func (sc *scope) evalSwitch(ss *ast.SwitchStmt) {
	sc = sc.enter("")
	if ss.Init != nil {
		sc.eval(ss.Init)
	}

	var tagval reflect.Value
	if ss.Tag != nil {
		tagval = sc.evalExpr(ss.Tag)[0]
	}

	for _, stmt := range ss.Body.List {
		clause := stmt.(*ast.CaseClause)

		var cases []reflect.Value
		for _, expr := range clause.List {
			cases = append(cases, sc.evalExpr(expr)[0])
		}

		if tagval != zeroval {
			for _, c := range cases {
				if tagval.Interface() == c.Interface() {
					for _, stmt := range clause.Body {
						sc.eval(stmt)
					}
					return
				}
			}
		} else {
			for _, c := range cases {
				if c.Bool() {
					for _, stmt := range clause.Body {
						sc.eval(stmt)
					}
					return
				}
			}
		}
	}
}

// evalCallExpr evaluates a call expression.
func (sc *scope) evalCallExpr(call *ast.CallExpr) []reflect.Value {
	var (
		recv      reflect.Value
		recvptr   reflect.Value
		fn        reflect.Value
		args      []reflect.Value
		varargs   reflect.Value
		method    bool
		mcallMode methodCallMode
		numargs   int
	)

	switch fexpr := call.Fun.(type) {
	case *ast.Ident:
		if f, ok := sc.lookupFunc(fexpr.Name); ok {
			fn = f
			break
		}
		switch fexpr.Name {
		case "make":
			return sc.evalBuiltinMake(call)
		case "delete":
			sc.evalBuiltinDelete(call)
			return nil
		case "close":
			sc.evalBuiltinClose(call)
			return nil
		case "append":
			return []reflect.Value{sc.evalBuiltinAppend(call)}
		case "len":
			return []reflect.Value{sc.evalBuiltinLen(call)}
		case "cap":
			return []reflect.Value{sc.evalBuiltinCap(call)}
		}
	case *ast.SelectorExpr:
		switch x := fexpr.X.(type) {
		case *ast.Ident:
			if x.Obj == nil {
				// stdlib
				if f, ok := sc.std[x.Name].Func[fexpr.Sel.Name]; ok {
					fn = f
				}
			} else {
				method = true
				recv, _ = sc.lookupValue(x.Name)
				vtype, _ := sc.valuetypes[x.Name]
				fn, mcallMode = sc.lookupMethod(vtype, fexpr)
			}
		default:
			sc.err("cannot handle selector of type %T", fexpr.X)
		}
	case *ast.FuncLit:
		fn = sc.evalFuncLit(fexpr)
	default:
		sc.err("cannot handle function expression of type %T", call.Fun)
	}

	if fn == zeroval {
		sc.err("no function found")
		return nil // unreachable
	}

	if method {
		switch mcallMode {
		case takeRecvAddr:
			recvptr = reflect.New(recv.Type())
			recvptr.Elem().Set(recv)
			args = append(args, recvptr)
		case dereferenceRecv:
			recv = recv.Elem()
			args = append(args, recv)
		default:
			// do nothing
			args = append(args, recv)
		}
	}

	fntype := fn.Type()

	if fntype.IsVariadic() {
		numargs = fntype.NumIn() - 1
		varargs = reflect.MakeSlice(fntype.In(numargs), 0, 0)
	} else {
		numargs = len(call.Args)
	}

	processed := 0
	for _, arg := range call.Args {
		for _, argval := range sc.evalExpr(arg) {
			idx := processed
			if method {
				idx++
			}
			if processed >= numargs {
				intyp := fntype.In(fntype.NumIn() - 1).Elem()
				if intyp.Kind() != reflect.Interface {
					varargs = reflect.Append(varargs, argval.Convert(intyp))
				} else {
					varargs = reflect.Append(varargs, argval)
				}
			} else {
				intyp := fntype.In(idx)
				if intyp.Kind() != reflect.Interface {
					args = append(args, argval.Convert(intyp))
				} else {
					args = append(args, argval)
				}

			}
			processed++
		}
	}

	var results []reflect.Value

	if fn.Type().IsVariadic() {
		results = fn.CallSlice(append(args, varargs))
	} else {
		results = fn.Call(args)
	}

	if method && mcallMode == takeRecvAddr {
		recv.Set(recvptr.Elem())
	}

	return results
}

type methodCallMode int

const (
	matchingType methodCallMode = iota
	takeRecvAddr
	dereferenceRecv
)

func (sc *scope) lookupMethod(vtype types.Type, se *ast.SelectorExpr) (reflect.Value, methodCallMode) {
	// Try the matching type for the receiver first.
	name := fmt.Sprintf("(%s).%s", vtype.String(), se.Sel.Name)
	if m, ok := sc.lookupFunc(name); ok {
		return m, matchingType
	}

	// Try the pointer type.
	name = fmt.Sprintf("(*%s).%s", vtype.String(), se.Sel.Name)
	if m, ok := sc.lookupFunc(name); ok {
		return m, takeRecvAddr
	}

	// Try the value type, if the type is a pointer.
	ptrtype, ok := vtype.(*types.Pointer)
	if !ok {
		return zeroval, -1
	}
	vtype = ptrtype.Elem()
	name = fmt.Sprintf("(%s).%s", vtype.String(), se.Sel.Name)
	if m, ok := sc.lookupFunc(name); ok {
		return m, dereferenceRecv
	}

	return zeroval, -1
}

// evalBuiltinMake calls the builtin make function.
func (sc *scope) evalBuiltinMake(call *ast.CallExpr) []reflect.Value {
	var argtype makeArgType
	switch ut := underlyingType(sc.typeinfo.Types[call.Args[0]].Type); ut.(type) {
	case *types.Slice:
		argtype = sliceMakeArg
	case *types.Map:
		argtype = mapMakeArg
	case *types.Chan:
		argtype = chanMakeArg
	default:
		sc.err("unknown underlying type %T for make call", ut)
		return nil // unreachable
	}

	switch len(call.Args) {
	case 1:
		switch argtype {
		case mapMakeArg:
			return []reflect.Value{sc.evalBuiltinMakeMap1(call)}
		case chanMakeArg:
			return []reflect.Value{sc.evalBuiltinMakeChan1(call)}
		}
		sc.err("unknown makeArgType %d", argtype)
		return nil // unreachable
	case 2:
		switch argtype {
		case sliceMakeArg:
			return []reflect.Value{sc.evalBuiltinMakeSlice2(call)}
		case mapMakeArg:
			return []reflect.Value{sc.evalBuiltinMakeMap2(call)}
		case chanMakeArg:
			return []reflect.Value{sc.evalBuiltinMakeChan2(call)}
		}
		sc.err("unknown makeArgType %d", argtype)
		return nil // unreachable
	case 3:
		if argtype != sliceMakeArg {
			sc.err("bogus argument type %v for 3-form slice make", argtype)
			return nil // unreachable
		}
		return []reflect.Value{sc.evalBuiltinMakeSlice3(call)}
	default:
		sc.err("%d arguments to make", len(call.Args))
		return nil // unreachable
	}
}

type makeArgType int

const (
	invalidMakeArg makeArgType = iota
	sliceMakeArg
	mapMakeArg
	chanMakeArg
)

func underlyingType(typ types.Type) types.Type {
	var t types.Type
	for t != typ {
		t = typ.Underlying()
	}
	return t
}

// evalBuiltinMakeSlice2 evaluates make([]T, 11) or make(SliceType, 12)
func (sc *scope) evalBuiltinMakeSlice2(call *ast.CallExpr) reflect.Value {
	typ := sc.typeOf(call.Args[0])
	size := sc.evalExpr(call.Args[1])[0].Int()
	return reflect.MakeSlice(typ, int(size), int(size))
}

// evalBuiltinMakeSlice3 evaluates make([]T, 11) or make(SliceType, 12)
func (sc *scope) evalBuiltinMakeSlice3(call *ast.CallExpr) reflect.Value {
	typ := sc.typeOf(call.Args[0])
	size := sc.evalExpr(call.Args[1])[0].Int()
	capacity := sc.evalExpr(call.Args[2])[0].Int()
	return reflect.MakeSlice(typ, int(size), int(capacity))
}

// evalBuiltinMakeMap1 evaluates make(map[K]V) or make(MapType).
func (sc *scope) evalBuiltinMakeMap1(call *ast.CallExpr) reflect.Value {
	typ := sc.typeOf(call.Args[0])
	return reflect.MakeMap(typ)
}

// evalBuiltinMakeMap2 evaluates make(map[K]V, 23) or make(MapType, 42).
func (sc *scope) evalBuiltinMakeMap2(call *ast.CallExpr) reflect.Value {
	typ := sc.typeOf(call.Args[0])
	size := sc.evalExpr(call.Args[1])[0].Int()
	return reflect.MakeMapWithSize(typ, int(size))
}

// evaluateBuiltinDelete evaluates delete(m, k).
func (sc *scope) evalBuiltinDelete(call *ast.CallExpr) {
	m := sc.evalExpr(call.Args[0])[0]
	k := sc.evalExpr(call.Args[1])[0]
	m.SetMapIndex(k, zeroval)
}

// evalBuiltinMakeChan1 evaluates make(chan T) or make(ChanType).
func (sc *scope) evalBuiltinMakeChan1(call *ast.CallExpr) reflect.Value {
	typ := sc.typeOf(call.Args[0])
	return reflect.MakeChan(typ, 0)
}

// evalBuiltinMakeChan2 evaluates make(chan T, 10) or make(ChanType, 20).
func (sc *scope) evalBuiltinMakeChan2(call *ast.CallExpr) reflect.Value {
	typ := sc.typeOf(call.Args[0])
	bufsize := sc.evalExpr(call.Args[1])[0].Int()
	return reflect.MakeChan(typ, int(bufsize))
}

// evalBuiltinClose evaluates close(ch).
func (sc *scope) evalBuiltinClose(call *ast.CallExpr) {
	ch := sc.evalExpr(call.Args[0])[0]
	ch.Close()
}

// evalBuiltinAppend evaluates append(s, x), append(s, y, z) or append(s, k...).
func (sc *scope) evalBuiltinAppend(call *ast.CallExpr) reflect.Value {
	sval := sc.evalExpr(call.Args[0])[0]
	varargs := reflect.MakeSlice(sval.Type(), 0, 0)

	for _, rexpr := range call.Args[1:] {
		for _, rval := range sc.evalExpr(rexpr) {
			if rval.Kind() == reflect.Slice {
				varargs = reflect.AppendSlice(varargs, rval)
			} else {
				varargs = reflect.Append(varargs, rval)
			}
		}
	}

	return reflect.AppendSlice(sval, varargs)
}

// evalBuiltinLen evaluates len(s).
func (sc *scope) evalBuiltinLen(call *ast.CallExpr) reflect.Value {
	val := sc.evalExpr(call.Args[0])[0]
	return reflect.ValueOf(val.Len())
}

// evalBuiltinCap evaluates cap(s).
func (sc *scope) evalBuiltinCap(call *ast.CallExpr) reflect.Value {
	val := sc.evalExpr(call.Args[0])[0]
	return reflect.ValueOf(val.Cap())
}

// evalIndexExpr evalueates b[0], s[x] = y and s["foo"] = 42.
func (sc *scope) evalIndexExpr(idx *ast.IndexExpr, val reflect.Value, okform bool) []reflect.Value {
	lhstype := sc.typeinfo.Types[idx.X].Type

	switch lhstype.(type) {
	case *types.Map:
		lhs := sc.evalExpr(idx.X)[0]
		key := sc.evalExpr(idx.Index)[0]

		if val != zeroval {
			lhs.SetMapIndex(key, val)
			return nil
		}
		mval := lhs.MapIndex(key)
		if mval == zeroval {
			mval = reflect.Zero(lhs.Type().Key())
		}
		if okform {
			ok := reflect.ValueOf(mval != zeroval)
			return []reflect.Value{mval, ok}
		}
		return []reflect.Value{mval}
	case *types.Slice:
		index := sc.evalExpr(idx.Index)[0].Int()
		sval := sc.evalExpr(idx.X)[0].Index(int(index))

		if val != zeroval {
			sval.Set(val)
			return nil
		}
		return []reflect.Value{sval}

	default:
		sc.err("cannot handle LHS expression of type %T in index expression", lhstype)
		return nil // unreachable
	}
}

// evalSliceExpr evaluates a slice expression.
func (sc *scope) evalSliceExpr(se *ast.SliceExpr) reflect.Value {
	sval := sc.evalExpr(se.X)[0]

	if se.Slice3 {
		var low, high, max int

		if se.Low != nil {
			low = int(sc.evalExpr(se.Low)[0].Int())
		}
		if se.High != nil {
			high = int(sc.evalExpr(se.High)[0].Int())
		} else {
			high = sval.Len()
		}
		if se.Max != nil {
			max = int(sc.evalExpr(se.Max)[0].Int())
		} else {
			max = sval.Cap()
		}

		return sval.Slice3(low, high, max)
	}

	var low, high int

	if se.Low != nil {
		low = int(sc.evalExpr(se.Low)[0].Int())
	}
	if se.High != nil {
		high = int(sc.evalExpr(se.High)[0].Int())
	} else {
		high = sval.Len()
	}

	return sval.Slice(low, high)
}

// evalIdent evaluates an identifier.
func (sc *scope) evalIdent(ident *ast.Ident) reflect.Value {
	if v, _ := sc.lookupValue(ident.Name); v != zeroval {
		return v
	}

	if cv, _ := sc.lookupConst(ident.Name); cv != (types.TypeAndValue{}) {
		val := cv.Value
		switch val.Kind() {
		case constant.Bool:
			return reflect.ValueOf(constant.BoolVal(val))
		case constant.String:
			return reflect.ValueOf(constant.StringVal(val))
		case constant.Int:
			intval, _ := constant.Int64Val(val)
			return reflect.ValueOf(intval)
		default:
			sc.err("cannot handle %v constant", val.String())
		}
	}

	sc.err("value for identifier %s not found", ident.Name)
	return zeroval // unreachable
}

// evalBasicLit evaluates a basic literal.
func (sc *scope) evalBasicLit(lit *ast.BasicLit) reflect.Value {
	switch lit.Kind {
	case token.INT:
		val, _ := strconv.Atoi(lit.Value)
		res := reflect.New(reflect.TypeOf(int(0)))
		res.Elem().Set(reflect.ValueOf(val))
		return res.Elem()
	case token.FLOAT:
		val, _ := strconv.ParseFloat(lit.Value, 64)
		res := reflect.New(reflect.TypeOf(float64(0)))
		res.Elem().Set(reflect.ValueOf(val))
		return res.Elem()
	case token.STRING:
		val, _ := strconv.Unquote(lit.Value)
		res := reflect.New(reflect.TypeOf(""))
		res.Elem().Set(reflect.ValueOf(val))
		return res.Elem()
	}

	sc.err("cannot evaluate %v basic literal", lit.Kind)
	return zeroval // unreachable
}

// evalUnaryExpr evaluates a unary expression.
func (sc *scope) evalUnaryExpr(ue *ast.UnaryExpr, okformrecv bool) []reflect.Value {
	switch ue.Op {
	case token.AND:
		val := sc.evalExpr(ue.X)[0]
		ptr := reflect.New(val.Type())
		ptr.Elem().Set(val)
		return []reflect.Value{ptr}
	case token.ARROW:
		val := sc.evalExpr(ue.X)[0]
		v, ok := val.Recv()
		if !ok {
			v = reflect.Zero(val.Type().Elem())
		}
		if okformrecv {
			if ok {
				return []reflect.Value{v, reflect.ValueOf(true)}
			}
			return []reflect.Value{v, reflect.ValueOf(false)}
		}
		return []reflect.Value{v}
	default:
		sc.err("cannot handle %v operand in unary expression", ue.Op)
		return nil // unreachable
	}
}

// evalBinaryExpr evaluates a binary expression.
func (sc *scope) evalBinaryExpr(be *ast.BinaryExpr) reflect.Value {
	x := sc.evalExpr(be.X)[0]
	y := sc.evalExpr(be.Y)[0]
	switch be.Op {
	case token.ADD:
		switch {
		case x.Type().ConvertibleTo(builtinType["int64"]):
			res := reflect.New(x.Type())
			res.Elem().SetInt(sc.evalIntAdd(x, y).Int())
			return res.Elem()
		case x.Type().ConvertibleTo(builtinType["string"]):
			res := reflect.New(x.Type())
			res.Elem().SetString(sc.evalStringAdd(x, y).String())
			return res.Elem()
		}
	case token.MUL:
		if x.Type().ConvertibleTo(builtinType["int64"]) {
			res := reflect.New(x.Type())
			res.Elem().SetInt(sc.evalIntMul(x, y).Int())
			return res.Elem()
		}
	case token.EQL:
		res := reflect.New(reflect.TypeOf(true))
		equal := reflect.DeepEqual(x.Interface(), y.Interface())
		res.Elem().SetBool(equal)
		return res.Elem()
	case token.LSS:
		if x.Type().ConvertibleTo(builtinType["int64"]) {
			res := reflect.New(reflect.TypeOf(true))
			less := x.Int() < y.Int()
			res.Elem().SetBool(less)
			return res.Elem()
		}
	}

	sc.err("cannot evaluate binary expression of type %v", be.Op)
	return zeroval // unreachable
}

// evalIntAdd evaluates x + y, where x and y are integers.
func (sc *scope) evalIntAdd(x, y reflect.Value) reflect.Value {
	return reflect.ValueOf(x.Int() + y.Int())
}

// evalIntMul evaluates x * y, where x and y are integers.
func (sc *scope) evalIntMul(x, y reflect.Value) reflect.Value {
	return reflect.ValueOf(x.Int() * y.Int())
}

// evalStringAdd evaluates x + y, where x and y are strings.
func (sc *scope) evalStringAdd(x, y reflect.Value) reflect.Value {
	return reflect.ValueOf(x.String() + y.String())
}

// evalCompositeLit evaluates a composite literal expression.
func (sc *scope) evalCompositeLit(cl *ast.CompositeLit) reflect.Value {
	typ := sc.typeOf(cl.Type)
	val := reflect.New(typ)

	for idx, elt := range cl.Elts {
		switch expr := elt.(type) {
		case *ast.KeyValueExpr:
			switch kexpr := expr.Key.(type) {
			case *ast.Ident:
				key := kexpr.Name
				exprval := sc.evalExpr(expr.Value)[0]
				val.Elem().FieldByName(key).Set(exprval)
			default:
				sc.err("cannot handle key expression of type %T in composite literal", expr.Key)
			}

		default:
			val.Elem().Field(idx).Set(sc.evalExpr(elt)[0])
		}
	}

	return val.Elem()
}

// evalSelectorExpr evaluates a selector expression.
func (sc *scope) evalSelectorExpr(se *ast.SelectorExpr) []reflect.Value {
	val := sc.evalExpr(se.X)[0]

	var values []reflect.Value

	if val.Kind() == reflect.Ptr {
		val = val.Elem()
	}

	switch kind := val.Kind(); kind {
	case reflect.Struct:
		values = append(values, val.FieldByName(se.Sel.Name))
	default:
		sc.err("cannot handle selector on value of kind %v", kind)
	}

	return values
}

// evalFuncLit evaluates a function literal expression.
func (sc *scope) evalFuncLit(fl *ast.FuncLit) reflect.Value {
	return sc.evalFuncDecl(nil, nil, fl.Type, fl.Body)
}

// evalFuncDecl evaluates a function declaration.
func (sc *scope) evalFuncDecl(recv *ast.FieldList, name *ast.Ident, ftype *ast.FuncType, body *ast.BlockStmt) reflect.Value {
	var (
		recvfield *ast.Field   // receiver, if any
		fparams   []*ast.Field // formal parameters, if any
		fresults  []*ast.Field // formal results, if any
	)
	if recv != nil {
		recvfield = recv.List[0]
	}
	if ftype.Params != nil {
		fparams = ftype.Params.List
	}
	if ftype.Results != nil {
		fresults = ftype.Results.List
	}

	fn := func(params []reflect.Value) []reflect.Value {
		var fnscope *scope
		if name != nil {
			fnscope = sc.enter(name.Name)
		} else {
			fnscope = sc.enter("")
		}
		if recvfield != nil {
			name := recvfield.Names[0].Name
			fnscope.values[name] = params[0]
			defer delete(fnscope.values, name)
			params = params[1:]
		}
		idx := 0
		for _, fparam := range fparams {
			for _, ident := range fparam.Names {
				name := ident.Name
				fnscope.values[name] = params[idx]
				defer delete(fnscope.values, name)
				idx++
			}
		}
		for _, fresult := range fresults {
			if len(fresult.Names) != 0 {
				fnscope.err("cannot handle named returns")
			}
		}
		for _, stmt := range body.List {
			_, isReturn := stmt.(*ast.ReturnStmt)
			values := fnscope.eval(stmt)
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
	rftype := reflect.FuncOf(argtypes, returntypes, variadic)
	rfn := reflect.MakeFunc(rftype, fn)

	if name != nil {
		sc.funcs[sc.funcName(name, recv)] = rfn
	}
	return rfn
}

// funcName returns the name of a function or method.
func (sc *scope) funcName(name *ast.Ident, recv *ast.FieldList) string {
	if recv == nil {
		return name.Name
	}
	rtype := recv.List[0].Type
	return fmt.Sprintf("(%s).%s", sc.typeName(rtype), name.Name)
}

// typeName returns the name of a type.
func (sc *scope) typeName(expr ast.Expr) string {
	return sc.typeinfo.Types[expr].Type.String()
}

// evalGenDecl evaluates a declaration.
func (sc *scope) evalGenDecl(gd *ast.GenDecl) {
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
		vspec := spec.(*ast.ValueSpec)
		for idx, name := range vspec.Names {
			vexpr := vspec.Values[idx]
			sc.consts[name.Name] = sc.typeinfo.Types[vexpr]
		}
	}
}

// evalVarDecl evaluates a variable declaration.
func (sc *scope) evalVarDecl(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		vspec := spec.(*ast.ValueSpec)
		for idx, name := range vspec.Names {
			var val reflect.Value
			if idx < len(vspec.Values) {
				val = sc.evalExpr(vspec.Values[idx])[0]
			} else {
				valptr := reflect.New(sc.typeOf(vspec.Type))
				val = valptr.Elem()
			}
			sc.values[name.Name] = val
		}
	}
}

// evalImportDecl evaluates an import declaration. Only standard library
// imports are supported for now.
func (sc *scope) evalImportDecl(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		i := spec.(*ast.ImportSpec)
		path := strings.Trim(i.Path.Value, `"`)
		stdpkg, ok := stdlib[path]
		if !ok {
			sc.err("non-stdlib import path %s", path)
		}

		sc.std[path] = stdpkg
	}
}

// evalTypeDecl evaluates a type declaration.
func (sc *scope) evalTypeDecl(gd *ast.GenDecl) {
	for _, spec := range gd.Specs {
		ts := spec.(*ast.TypeSpec)
		name := fmt.Sprintf("%s.%s", sc.pkg.Name(), ts.Name)
		typ := sc.typeOf(ts.Type)
		sc.types[name] = typ
	}
}

// lookupValue looks up a value. It starts from the current scope, and
// walks the parent scopes if necessary. If the value is not found in the
// current scope, lookupValue returns false. It returns a reflect.Value
// v such that v.CanSet() == true. If no such value exists in any scope,
// it returns zeroval.
func (sc *scope) lookupValue(name string) (v reflect.Value, local bool) {
	v, ok := sc.values[name]
	if ok {
		return v, true
	}

	for sc = sc.parent; sc != nil; sc = sc.parent {
		v, ok := sc.values[name]
		if ok {
			return v, false
		}
	}

	return zeroval, false
}

// lookupConst looks up a constant. Analogous to lookupValue.
func (sc *scope) lookupConst(name string) (types.TypeAndValue, bool) {
	tv, ok := sc.consts[name]
	if ok {
		return tv, true
	}

	for sc = sc.parent; sc != nil; sc = sc.parent {
		tv, ok := sc.consts[name]
		if ok {
			return tv, false
		}
	}

	return types.TypeAndValue{}, false
}

// lookupFunc looks up a runtime function value.
func (sc *scope) lookupFunc(name string) (reflect.Value, bool) {
	for sc != nil {
		if fn, ok := sc.funcs[name]; ok {
			return fn, true
		}
		if fn, ok := sc.lookupValue(name); ok {
			return fn, true
		}

		sc = sc.parent
	}
	return zeroval, false
}

// enter enters a new scope.
func (sc *scope) enter(name string) *scope {
	child := newScope(sc)
	return child
}

func (sc *scope) err(format string, args ...interface{}) {
	panic(interpreterError(fmt.Sprintf(format, args...)))
}

type interpreterError string

func (e interpreterError) Error() string { return string(e) }

var builtinType = map[string]reflect.Type{
	"bool":          reflect.TypeOf(true),
	"byte":          reflect.TypeOf(byte(0)),
	"complex128":    reflect.TypeOf(complex(float64(0), float64(0))),
	"complex64":     reflect.TypeOf(complex(float32(0), float32(0))),
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
	return sc.typeOf(f.Type)
}

func (sc *scope) typeOf(expr ast.Expr) reflect.Type {
	return sc.dynamicType(sc.typeinfo.Types[expr].Type)
}

func (sc *scope) dynamicType(typ types.Type) reflect.Type {
	switch t := typ.(type) {
	case *types.Array:
		size := int(t.Len())
		return reflect.ArrayOf(size, sc.dynamicType(t.Elem()))

	case *types.Chan:
		dir := reflectChanDir(t.Dir())
		return reflect.ChanOf(dir, sc.dynamicType(t.Elem()))

	case *types.Basic:
		return builtinType[basicKind[t.Kind()]]

	case *types.Map:
		ktype := sc.dynamicType(t.Key())
		etype := sc.dynamicType(t.Elem())
		return reflect.MapOf(ktype, etype)

	case *types.Named:
		return sc.dynamicType(t.Underlying())

	case *types.Pointer:
		return reflect.PtrTo(sc.dynamicType(t.Elem()))

	case *types.Slice:
		return reflect.SliceOf(sc.dynamicType(t.Elem()))

	case *types.Struct:
		var fields []reflect.StructField

		for i := 0; i < t.NumFields(); i++ {
			field := t.Field(i)
			sf := reflect.StructField{
				Name:      field.Name(),
				Type:      sc.dynamicType(field.Type()),
				Tag:       reflect.StructTag(t.Tag(i)),
				Anonymous: field.Anonymous(),
			}
			fields = append(fields, sf)
		}

		return reflect.StructOf(fields)

	case *types.Interface:
		// !!!!!!!!
		var x chan interface{}
		return reflect.TypeOf(x).Elem()

	default:
		sc.err("cannot handle dynamic type of %T", typ)
		return nil // unreachable
	}
}

func reflectChanDir(dir types.ChanDir) reflect.ChanDir {
	switch dir {
	case types.SendRecv:
		return reflect.BothDir
	case types.SendOnly:
		return reflect.SendDir
	case types.RecvOnly:
		return reflect.RecvDir
	default:
		return -1
	}
}

var zeroval = reflect.Value{}
