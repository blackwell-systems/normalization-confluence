package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
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
	for _, c := range []struct{ json, pkg, out string }{
		{"../oracle_core.json", "oracle", "../oracle/oracle_gen.go"},
		{"../primref_mapped.json", "mapped", "../primcheck/mapped/primref_gen.go"},
		{"../primref_plain.json", "plain", "../primcheck/plain/primref_gen.go"},
		{"../fixture.json", "fixture", "../fixture/fixture_gen.go"},
	} {
		raw := read(t, c.json)
		a, err := Generate(raw, c.pkg, c.json)
		if err != nil {
			t.Fatalf("%s: %v", c.json, err)
		}
		b, err := Generate(raw, c.pkg, c.json)
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
