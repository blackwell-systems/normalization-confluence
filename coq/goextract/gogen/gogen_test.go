package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

func read(t *testing.T, path string) []byte {
	t.Helper()
	b, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// The committed Go is exactly what gogen generates from the committed JSON,
// and generating twice gives the same bytes.
func TestCommittedOutputIsCurrent(t *testing.T) {
	for _, c := range []struct {
		json, pkg, out string
		opts           Options
	}{
		{"../oracle_core.json", "oracle", "../oracle/oracle_gen.go", Options{}},
		{"../primref_mapped.json", "mapped", "../primcheck/mapped/primref_gen.go", Options{}},
		{"../primref_plain.json", "plain", "../primcheck/plain/primref_gen.go", Options{}},
		{"../fixture.json", "fixture", "../fixture/fixture_gen.go", Options{}},
		{"../semantics.json", "semantics", "../semantics/semantics_gen.go", Options{}},
	} {
		c.opts = allowFor(t, c.json)
		raw := read(t, c.json)
		a, err := GenerateWith(raw, c.pkg, c.json, c.opts)
		if err != nil {
			t.Fatalf("%s: %v", c.json, err)
		}
		b, err := GenerateWith(raw, c.pkg, c.json, c.opts)
		if err != nil || !bytes.Equal(a, b) {
			t.Fatalf("%s: two generations differ (err %v)", c.json, err)
		}
		if !bytes.Equal(a, read(t, c.out)) {
			t.Errorf("%s is stale: regenerate it from %s (make -C coq/goextract gen)", c.out, c.json)
		}
	}
}

func decls(t *testing.T, path string) map[string]string {
	t.Helper()
	var root struct {
		Declarations []json.RawMessage `json:"declarations"`
	}
	if err := json.Unmarshal(read(t, path), &root); err != nil {
		t.Fatal(err)
	}
	out := map[string]string{}
	for _, d := range root.Declarations {
		var h struct {
			Name    any               `json:"name"`
			Fixlist []json.RawMessage `json:"fixlist"`
		}
		json.Unmarshal(d, &h)
		if s, ok := h.Name.(string); ok {
			out[s] = string(d)
		}
		for _, f := range h.Fixlist {
			var fh struct{ Name string }
			json.Unmarshal(f, &fh)
			out[fh.Name] = string(f)
		}
	}
	return out
}

// Every prim gogen knows has a reference in PrimRef.v, and under ExtrGo.v that
// reference really is the prim (otherwise primcheck would compare a Rocq
// definition with itself).
func TestEveryPrimHasAReference(t *testing.T) {
	mapped := decls(t, "../primref_mapped.json")
	check := string(read(t, "../primcheck/primcheck_test.go"))
	for name := range prims {
		ref := "ref_" + strings.TrimPrefix(name, "prim_")
		body, ok := mapped[ref]
		if !ok {
			t.Errorf("%s: no %s in PrimRef.v", name, ref)
			continue
		}
		if !strings.Contains(body, `"name": "`+name+`"`) {
			t.Errorf("%s does not extract to %s under ExtrGo.v (the directive does not catch the constant)", ref, name)
		}
		if !strings.Contains(check, "M.F_"+ref) || !strings.Contains(check, "P.F_"+ref) {
			t.Errorf("%s: primcheck does not compare %s with its Rocq definition", name, ref)
		}
	}
}

// Every mapped constructor is built and matched by some probe in PrimRef.v.
func TestEveryMappedConstructorIsProbed(t *testing.T) {
	mapped := decls(t, "../primref_mapped.json")
	var probes strings.Builder
	for name, body := range mapped {
		if strings.HasPrefix(name, "probe_") || strings.HasPrefix(name, "ref_") {
			probes.WriteString(body)
		}
	}
	all := probes.String()
	for tn, mt := range mappedTypes {
		for cn := range mt.ctors {
			if !strings.Contains(all, `"what": "pat:constructor", "name": "`+cn+`"`) {
				t.Errorf("%s.%s is never matched by a probe", tn, cn)
			}
			if !strings.Contains(all, `"what": "expr:constructor", "name": "`+cn+`"`) {
				t.Errorf("%s.%s is never built by a probe", tn, cn)
			}
		}
	}
}

func mustRefuse(t *testing.T, what, js, want string) {
	t.Helper()
	_, err := Generate([]byte(js), "p", "x.json")
	if err == nil || !strings.Contains(err.Error(), want) {
		t.Errorf("%s: want a refusal mentioning %q, got %v", what, want, err)
	}
}

const modHead = `{"what": "module", "name": "m", "need_magic": false, "need_dummy": false, "used_modules": [], "declarations": [`

// Input outside the accepted fragment is refused, never guessed at.
func TestRefusals(t *testing.T) {
	mustRefuse(t, "unknown node kind",
		modHead+`{"what": "decl:mystery", "name": "x"}]}`, "unsupported node kind")
	mustRefuse(t, "unknown key",
		modHead+`{"what": "decl:term", "name": "x", "type": {"what": "type:glob", "name": "go_nat", "args": []}, "value": {"what": "expr:constructor", "name": "nat_0", "args": []}, "extra": 1}]}`, "has keys")
	mustRefuse(t, "missing key",
		modHead+`{"what": "decl:term", "name": "x", "value": {"what": "expr:constructor", "name": "nat_0", "args": []}}]}`, "has keys")
	mustRefuse(t, "Obj.magic",
		`{"what": "module", "name": "m", "need_magic": true, "need_dummy": false, "used_modules": [], "declarations": []}`, "Obj.magic")
	mustRefuse(t, "modular extraction",
		`{"what": "module", "name": "m", "need_magic": false, "need_dummy": false, "used_modules": ["Foo"], "declarations": []}`, "used_modules")
	mustRefuse(t, "unknown prim",
		modHead+`{"what": "decl:term", "name": "prim_frobnicate", "type": {"what": "type:glob", "name": "go_nat", "args": []}, "value": {"what": "expr:exception", "msg": "UNUSED"}}]}`, "unknown prim")
	mustRefuse(t, "unknown mapped type",
		modHead+`{"what": "decl:ind", "name": "go_float", "argnames": [], "constructors": []}]}`, "unknown mapped type")
	mustRefuse(t, "mapped type with a different shape",
		modHead+`{"what": "decl:ind", "name": "go_nat", "argnames": [], "constructors": [{"name": "nat_0", "argtypes": []}]}]}`, "unexpected shape")
	mustRefuse(t, "duplicate global",
		modHead+`{"what": "decl:term", "name": "x", "type": {"what": "type:glob", "name": "go_nat", "args": []}, "value": {"what": "expr:constructor", "name": "nat_0", "args": []}},
		{"what": "decl:term", "name": "x", "type": {"what": "type:glob", "name": "go_nat", "args": []}, "value": {"what": "expr:constructor", "name": "nat_0", "args": []}}]}`, "duplicate global")
	mustRefuse(t, "ill-typed body",
		modHead+`{"what": "decl:term", "name": "x", "type": {"what": "type:glob", "name": "go_nat", "args": []}, "value": {"what": "expr:constructor", "name": "true", "args": []}}]}`, "cannot unify")
	mustRefuse(t, "unbound variable",
		modHead+`{"what": "decl:term", "name": "x", "type": {"what": "type:glob", "name": "go_nat", "args": []}, "value": {"what": "expr:rel", "name": "y"}}]}`, "unbound variable")
}

func TestGenerateHeaderUsesBaseName(t *testing.T) {
	src, err := Generate([]byte(modHead+`]}`), "p", filepath.Join("some", "dir", "x.json"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.HasPrefix(string(src), "// Code generated by gogen from x.json (module m). DO NOT EDIT.") {
		t.Errorf("header: %q", strings.SplitN(string(src), "\n", 2)[0])
	}
}

// unaryAdd is the shape PeanoNat's Nat.add extracts to when it is not mapped:
// a fixpoint over go_nat that recurses once per unit of its argument.
const unaryAdd = `{"what": "decl:fixgroup", "fixlist": [{"what": "fixgroup:item", "name": "add",
  "type": {"what": "type:arrow", "left": {"what": "type:glob", "name": "go_nat", "args": []},
           "right": {"what": "type:arrow", "left": {"what": "type:glob", "name": "go_nat", "args": []},
                     "right": {"what": "type:glob", "name": "go_nat", "args": []}}},
  "value": {"what": "expr:lambda", "argnames": ["n", "m"], "body": {"what": "expr:case", "expr": {"what": "expr:rel", "name": "n"}, "cases": [
    {"what": "case", "pat": {"what": "pat:constructor", "name": "nat_0", "argnames": []}, "body": {"what": "expr:rel", "name": "m"}},
    {"what": "case", "pat": {"what": "pat:constructor", "name": "nat_succ", "argnames": ["p"]},
     "body": {"what": "expr:constructor", "name": "nat_succ", "args": [{"what": "expr:apply", "func": {"what": "expr:global", "name": "add"}, "args": [{"what": "expr:rel", "name": "p"}, {"what": "expr:rel", "name": "m"}]}]}}]}}}]}`

// Unary recursion on a nat (Nat.add, Nat.mul, Nat.pow extracted as their Rocq
// definitions, Pos.of_succ_nat, ...) costs time, and stack unless it is a tail
// call, linear in the number. It is refused unless allowed by name.
func TestRefusesUnaryArithmetic(t *testing.T) {
	js := modHead + unaryAdd + `]}`
	if _, err := Generate([]byte(js), "p", "x.json"); err == nil || !strings.Contains(err.Error(), "unary nat recursion: add") {
		t.Fatalf("want a refusal naming add, got %v", err)
	}
	if _, err := GenerateWith([]byte(js), "p", "x.json", Options{AllowUnary: []string{"add"}}); err != nil {
		t.Fatalf("allowed by name: %v", err)
	}
}

// allowFor is what make gen allows for an extraction: allow-unary.txt's list,
// or everything when GOEXTRACT_UNARY=any (a prover other than the reference).
func allowFor(t *testing.T, json string) Options {
	if os.Getenv("GOEXTRACT_UNARY") == "any" {
		return Options{AllowUnary: []string{"*"}}
	}
	return Options{AllowUnary: AllowedFor(string(read(t, "../allow-unary.txt")), filepath.Base(json))}
}

// allow-unary.txt lists exactly the unary recursions each extraction has: no
// entry is missing (generation would fail) and none is stale. The semantics
// list includes Pos.of_succ_nat, which Z.of_nat extracts through: a recursion
// the earlier name-based check missed.
func TestUnaryRecursionIsExactlyTheAllowList(t *testing.T) {
	if os.Getenv("GOEXTRACT_UNARY") == "any" {
		t.Skip("another prover's standard library")
	}
	file := string(read(t, "../allow-unary.txt"))
	for _, json := range []string{"oracle_core.json", "primref_mapped.json", "primref_plain.json", "fixture.json", "semantics.json"} {
		want := AllowedFor(file, json)
		sort.Strings(want)
		_, err := Generate(read(t, "../"+json), "p", json)
		switch {
		case len(want) == 0 && err != nil:
			t.Errorf("%s: %v", json, err)
		case len(want) > 0 && (err == nil || !strings.Contains(err.Error(), "unary nat recursion: "+strings.Join(want, ", ")+" (")):
			t.Errorf("%s: allow-unary.txt lists %v; without it gogen says %v", json, want, err)
		}
	}
	if !strings.Contains(file, "semantics.json      of_succ_nat ") {
		t.Error("the of_succ_nat case is gone from allow-unary.txt")
	}
}

const natTy = `{"what": "type:glob", "name": "go_nat", "args": []}`

func natFun(name, body string) string {
	return `{"what": "decl:term", "name": "` + name + `", "type": {"what": "type:arrow", "left": ` + natTy + `, "right": ` + natTy + `},
  "value": {"what": "expr:lambda", "argnames": ["n"], "body": ` + body + `}}`
}

func TestRefusesMalformedPrograms(t *testing.T) {
	zero := `{"what": "expr:constructor", "name": "nat_0", "args": []}`
	// A wildcard before another case: ML takes the first match, a Go switch
	// takes default last, so the two would disagree.
	mustRefuse(t, "non-final wildcard", modHead+natFun("f", `{"what": "expr:case", "expr": {"what": "expr:rel", "name": "n"}, "cases": [
		{"what": "case", "pat": {"what": "pat:wild"}, "body": `+zero+`},
		{"what": "case", "pat": {"what": "pat:constructor", "name": "nat_0", "argnames": []}, "body": `+zero+`}]}`)+`]}`, "not the last case")
	mustRefuse(t, "non-final variable pattern", modHead+natFun("f", `{"what": "expr:case", "expr": {"what": "expr:rel", "name": "n"}, "cases": [
		{"what": "case", "pat": {"what": "pat:rel", "name": "m"}, "body": `+zero+`},
		{"what": "case", "pat": {"what": "pat:constructor", "name": "nat_0", "argnames": []}, "body": `+zero+`}]}`)+`]}`, "not the last case")
	// The same name bound twice in one binder list.
	mustRefuse(t, "duplicate lambda binders", modHead+`{"what": "decl:term", "name": "f", "type": {"what": "type:arrow", "left": `+natTy+`, "right": {"what": "type:arrow", "left": `+natTy+`, "right": `+natTy+`}},
  "value": {"what": "expr:lambda", "argnames": ["x", "x"], "body": {"what": "expr:rel", "name": "x"}}}]}`, "binds x twice")
	// need_magic must be a boolean.
	mustRefuse(t, "need_magic not a boolean",
		`{"what": "module", "name": "m", "need_magic": "no", "need_dummy": false, "used_modules": [], "declarations": []}`, "need_magic")
}

// An absurd branch (extracted as an exception) compiles to a panic with
// nothing after it, in and out of tail position, so the output is vet-clean.
func TestExceptionIsATerminatingPanic(t *testing.T) {
	exc := `{"what": "expr:exception", "msg": "absurd case"}`
	src, err := Generate([]byte(modHead+natFun("f", `{"what": "expr:case", "expr": {"what": "expr:rel", "name": "n"}, "cases": [
		{"what": "case", "pat": {"what": "pat:constructor", "name": "nat_0", "argnames": []}, "body": `+exc+`},
		{"what": "case", "pat": {"what": "pat:constructor", "name": "nat_succ", "argnames": ["k"]},
		 "body": {"what": "expr:constructor", "name": "nat_succ", "args": [{"what": "expr:case", "expr": {"what": "expr:rel", "name": "k"}, "cases": [
			{"what": "case", "pat": {"what": "pat:constructor", "name": "nat_0", "argnames": []}, "body": `+exc+`},
			{"what": "case", "pat": {"what": "pat:wild"}, "body": {"what": "expr:rel", "name": "k"}}]}]}}]}`)+`]}`), "p", "x.json")
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(src), "*new(") {
		t.Errorf("an exception leaves code after its panic:\n%s", src)
	}
}

// A match on a mapped number first checks that the value is in its type, so a
// value outside it (a negative nat, a positive below 1) panics even when the
// match has a wildcard.
func TestMatchOnAMappedNumberChecksItsDomain(t *testing.T) {
	src, err := Generate([]byte(modHead+natFun("f", `{"what": "expr:case", "expr": {"what": "expr:rel", "name": "n"}, "cases": [
		{"what": "case", "pat": {"what": "pat:constructor", "name": "nat_0", "argnames": []}, "body": {"what": "expr:rel", "name": "n"}},
		{"what": "case", "pat": {"what": "pat:wild"}, "body": {"what": "expr:rel", "name": "n"}}]}`)+`]}`), "p", "x.json")
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(src), "< 0 {") || !strings.Contains(string(src), "not a nat") {
		t.Errorf("no domain check before the match:\n%s", src)
	}
}

// GuardCoind.v covers every entry point gogen translates.
func TestGuardCoversEveryEntryPoint(t *testing.T) {
	guard := string(read(t, "../GuardCoind.v"))
	for _, f := range []string{"../ExtractGo.v", "../ExtractPrimMapped.v", "../ExtractFixture.v", "../ExtractSemantics.v"} {
		src := string(read(t, f))
		for _, chunk := range strings.Split(src, "Extraction \"")[1:] {
			names := strings.Fields(strings.SplitN(strings.SplitN(chunk, "\"", 2)[1], ".", 2)[0])
			for _, n := range names {
				if !strings.Contains(guard, " "+n+" ") && !strings.Contains(guard, " "+n+".") && !strings.Contains(guard, " "+n+"\n") {
					t.Errorf("%s extracts %s, which GuardCoind.v does not check", f, n)
				}
			}
		}
	}
}

// Programs from the review that gogen must refuse (testdata/refuse): an axiom,
// a let-bound polymorphic function used at two types, a type that needs
// Obj.magic, and a local fixpoint in argument position.
func TestRefusesReviewPrograms(t *testing.T) {
	for file, want := range map[string]string{
		"r_axiom.json":    "expr:axiom",
		"r_letpoly.json":  "cannot unify",
		"r_magic.json":    "type:unknown",
		"r_localfix.json": "expr:fix",
	} {
		_, err := Generate(read(t, filepath.Join("testdata", "refuse", file)), "p", file)
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%s: want a refusal mentioning %q, got %v", file, want, err)
		}
	}
}
