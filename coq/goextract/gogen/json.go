package main

import (
	"encoding/json"
	"fmt"
	"sort"
	"strings"
)

// Node is one node of Rocq's MiniML JSON extraction (plugins/extraction/json.ml).
// Decoding is strict: every node kind gogen accepts has a fixed key set, and an
// unknown kind or key is an error, so a change in the extraction's output can
// not be silently misread.
type Node struct {
	What      string
	Name      string
	Argnames  []string
	Body      *Node
	Expr      *Node
	Cases     []*Node
	Pat       *Node
	Func      *Node
	Args      []*Node // expression arguments, or type arguments
	Nameval   *Node
	Value     *Node
	Type      *Node
	Left      *Node
	Right     *Node
	Fixlist   []*Node
	Ctors     []*Ctor
	Msg       string
	Decls     []*Node
	NeedMagic bool
	NeedDummy bool
}

// Ctor is one constructor of an inductive declaration.
type Ctor struct {
	Name     string
	Argtypes []*Node
}

// keys lists, for each node kind, exactly the keys it carries.
var keys = map[string][]string{
	"module":           {"declarations", "name", "need_dummy", "need_magic", "used_modules"},
	"decl:ind":         {"argnames", "constructors", "name"},
	"decl:type":        {"argnames", "name", "value"},
	"decl:term":        {"name", "type", "value"},
	"decl:fixgroup":    {"fixlist"},
	"fixgroup:item":    {"name", "type", "value"},
	"expr:rel":         {"name"},
	"expr:global":      {"name"},
	"expr:apply":       {"args", "func"},
	"expr:lambda":      {"argnames", "body"},
	"expr:let":         {"body", "name", "nameval"},
	"expr:constructor": {"args", "name"},
	"expr:case":        {"cases", "expr"},
	"expr:exception":   {"msg"},
	"case":             {"body", "pat"},
	"pat:constructor":  {"argnames", "name"},
	"pat:wild":         {},
	"pat:rel":          {"name"},
	"type:arrow":       {"left", "right"},
	"type:glob":        {"args", "name"},
	"type:var":         {"name"},
	"type:varidx":      {"name"},
}

func decode(raw json.RawMessage, where string) *Node {
	var m map[string]json.RawMessage
	if err := json.Unmarshal(raw, &m); err != nil {
		fail("%s: %v", where, err)
	}
	var what string
	if err := json.Unmarshal(m["what"], &what); err != nil {
		fail("%s: node without a kind", where)
	}
	allowed, ok := keys[what]
	if !ok {
		fail("%s: unsupported node kind %s", where, what)
	}
	got := []string{}
	for k := range m {
		if k != "what" {
			got = append(got, k)
		}
	}
	sort.Strings(got)
	if strings.Join(got, ",") != strings.Join(allowed, ",") {
		fail("%s: %s has keys %v, expected %v", where, what, got, allowed)
	}
	n := &Node{What: what}
	at := where + "/" + what
	str := func(k string) string {
		var s string
		if json.Unmarshal(m[k], &s) == nil {
			return s
		}
		var i int64
		if json.Unmarshal(m[k], &i) == nil { // type:varidx names are integers
			return fmt.Sprint(i)
		}
		fail("%s: %s is neither a string nor an integer", at, k)
		return ""
	}
	one := func(k string) *Node { return decode(m[k], at+"."+k) }
	list := func(k string) []*Node {
		var rs []json.RawMessage
		if err := json.Unmarshal(m[k], &rs); err != nil {
			fail("%s.%s: %v", at, k, err)
		}
		out := make([]*Node, len(rs))
		for i, r := range rs {
			out[i] = decode(r, fmt.Sprintf("%s.%s[%d]", at, k, i))
		}
		return out
	}
	strs := func(k string) []string {
		var ss []string
		if err := json.Unmarshal(m[k], &ss); err != nil {
			fail("%s.%s: %v", at, k, err)
		}
		return ss
	}
	for _, k := range allowed {
		switch k {
		case "name":
			n.Name = str(k)
		case "argnames":
			n.Argnames = strs(k)
		case "body":
			n.Body = one(k)
		case "expr":
			n.Expr = one(k)
		case "cases":
			n.Cases = list(k)
		case "pat":
			n.Pat = one(k)
		case "func":
			n.Func = one(k)
		case "args":
			n.Args = list(k)
		case "nameval":
			n.Nameval = one(k)
		case "value":
			n.Value = one(k)
		case "type":
			n.Type = one(k)
		case "left":
			n.Left = one(k)
		case "right":
			n.Right = one(k)
		case "fixlist":
			n.Fixlist = list(k)
		case "declarations":
			n.Decls = list(k)
		case "msg":
			n.Msg = str(k)
		case "need_magic":
			json.Unmarshal(m[k], &n.NeedMagic)
		case "need_dummy":
			json.Unmarshal(m[k], &n.NeedDummy)
		case "used_modules":
			if strs(k) != nil && len(strs(k)) > 0 {
				fail("%s: used_modules %v (modular extraction is not supported)", at, strs(k))
			}
		case "constructors":
			var cs []struct {
				Name     string            `json:"name"`
				Argtypes []json.RawMessage `json:"argtypes"`
			}
			if err := json.Unmarshal(m[k], &cs); err != nil {
				fail("%s.constructors: %v", at, err)
			}
			for _, c := range cs {
				ct := &Ctor{Name: c.Name}
				for i, a := range c.Argtypes {
					ct.Argtypes = append(ct.Argtypes, decode(a, fmt.Sprintf("%s.%s[%d]", at, c.Name, i)))
				}
				n.Ctors = append(n.Ctors, ct)
			}
		}
	}
	return n
}
