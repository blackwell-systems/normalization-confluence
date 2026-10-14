package db

import (
	"context"
	"net/http"
	"testing"

	"github.com/couchbase/sync_gateway/base"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Local check of prediction P4: an older ISGR tombstone applied on top of a newer tombstone from the same source.
// Each write uses the PutDocOptions processRev builds on the active pull side of an sgr2 replication with the
// default resolver.

const p4SrcB = "c3JjQg" // remote cluster B's source ID

type p4State struct {
	cas     uint64
	seq     uint64
	deleted bool
	winner  string
	leaves  []string
	hlv     HybridLogicalVector
}

func p4Read(t *testing.T, ctx context.Context, collection *DatabaseCollectionWithUser, docID string) p4State {
	doc, err := collection.GetDocument(ctx, docID, DocUnmarshalAll)
	require.NoError(t, err)
	require.NotNil(t, doc.HLV)
	return p4State{
		cas:     doc.Cas,
		seq:     doc.Sequence,
		deleted: doc.IsDeleted(),
		winner:  doc.GetRevTreeID(),
		leaves:  doc.History.GetLeaves(),
		hlv:     *doc.HLV.Copy(),
	}
}

func p4Log(t *testing.T, label string, s p4State) {
	t.Logf("%-28s cas=%d seq=%d deleted=%v winner=%s leaves=%v cv=%s@%d pv=%v mv=%v",
		label, s.cas, s.seq, s.deleted, s.winner, s.leaves, s.hlv.SourceID, s.hlv.Version, s.hlv.PreviousVersions, s.hlv.MergeVersions)
}

// p4ApplyISGRRev mirrors processRev (blip_handler.go) for an HLV rev from an sgr2 peer.
func p4ApplyISGRRev(ctx context.Context, collection *DatabaseCollectionWithUser, docID string, body Body, deleted bool, hlv *HybridLogicalVector, revTree []string, resolver *ConflictResolver) error {
	newDoc := CreateTestDocument(docID, revTree[0], body, deleted, 0)
	opts := PutDocOptions{
		NewDoc:                         newDoc,
		RevTreeHistory:                 revTree,
		ForceAllowConflictingTombstone: deleted, // set at both sgr2 ends for an incoming tombstone
		NewDocHLV:                      hlv,
		ConflictResolver:               resolver,
		ISGRWrite:                      true,
	}
	_, _, _, err := collection.PutExistingCurrentVersion(ctx, opts)
	return err
}

func p4Setup(t *testing.T) (*Database, context.Context, *DatabaseCollectionWithUser, *ConflictResolver) {
	db, ctx := SetupTestDB(t)
	collection, ctx := GetSingleDatabaseCollectionWithUser(ctx, t, db)
	return db, ctx, collection, NewConflictResolver(DefaultLWWConflictResolutionType, nil)
}

// TestP4ISGRStaleTombstoneOverTombstone: x0 (local, srcA), then tb3 (srcB:+30), then the older tb1 (srcB:+10).
func TestP4ISGRStaleTombstoneOverTombstone(t *testing.T) {
	db, ctx, collection, resolver := p4Setup(t)
	defer db.Close(ctx)
	const docID = "p4doc"

	rev1, _, err := collection.Put(ctx, docID, Body{"v": "x0"})
	require.NoError(t, err)
	x0 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after x0 (local write)", x0)
	srcA, aVal := x0.hlv.SourceID, x0.hlv.Version
	b10, b30 := aVal+10, aVal+30
	t.Logf("srcA=%s aVal=%d srcB=%s b10=%d b30=%d", srcA, aVal, p4SrcB, b10, b30)

	// tb3 on B: tb1 (2-), b2 (3-), tb3 (4-); B's HLV carries srcA:aVal in pv
	tb3HLV := &HybridLogicalVector{SourceID: p4SrcB, Version: b30, PreviousVersions: HLVVersions{srcA: aVal}}
	err = p4ApplyISGRRev(ctx, collection, docID, Body{}, true, tb3HLV, []string{"4-c3", "3-b2", "2-a1", rev1}, resolver)
	t.Logf("tb3 write err=%v", err)
	require.NoError(t, err)
	afterTb3 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after tb3", afterTb3)
	require.True(t, afterTb3.deleted)
	require.Equal(t, p4SrcB, afterTb3.hlv.SourceID)
	require.Equal(t, b30, afterTb3.hlv.Version)

	// tb1 from B, delivered after tb3 committed (the CAS-retry re-run sees this state)
	tb1HLV := &HybridLogicalVector{SourceID: p4SrcB, Version: b10, PreviousVersions: HLVVersions{srcA: aVal}}
	err = p4ApplyISGRRev(ctx, collection, docID, Body{}, true, tb1HLV, []string{"2-a1", rev1}, resolver)
	t.Logf("tb1 write err=%v", err)
	afterTb1 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after tb1", afterTb1)
	t.Logf("tb1 persisted (cas changed): %v", afterTb1.cas != afterTb3.cas)

	// the P4 claim: cv regresses to srcB:b10 and srcB:b30 is gone from the HLV
	assert.NoError(t, err, "claim: tb1 write is not rejected")
	assert.NotEqual(t, afterTb3.cas, afterTb1.cas, "claim: tb1 write is not cancelled")
	assert.Equal(t, p4SrcB, afterTb1.hlv.SourceID, "claim: cv source")
	assert.Equal(t, b10, afterTb1.hlv.Version, "claim: cv regresses to srcB:b10")
	assert.NotContains(t, afterTb1.hlv.PreviousVersions, p4SrcB, "claim: srcB:b30 not retained in pv")
	assert.NotContains(t, afterTb1.hlv.MergeVersions, p4SrcB, "claim: srcB:b30 not retained in mv")
	assert.Equal(t, "4-c3", afterTb1.winner, "rev tree winner stays tb3")

	// a4: local re-create on A, PUT without _rev on the tombstone
	_, _, err = collection.Put(ctx, docID, Body{"v": "a4"})
	t.Logf("a4 local put err=%v", err)
	require.NoError(t, err)
	a4 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after a4 (local write)", a4)
	a4Doc, err := collection.GetDocument(ctx, docID, DocUnmarshalAll)
	require.NoError(t, err)
	a4History, err := a4Doc.History.getHistory(a4.winner)
	require.NoError(t, err)
	t.Logf("a4 rev tree history sent with push: %v", a4History)

	// passive side B: holds x0 then tb3 (cv srcB:b30); A pushes a4
	const docB = "p4docB"
	err = p4ApplyISGRRev(ctx, collection, docB, Body{"v": "x0"}, false, &HybridLogicalVector{SourceID: srcA, Version: aVal}, []string{rev1}, nil)
	require.NoError(t, err)
	bTb3 := &HybridLogicalVector{SourceID: p4SrcB, Version: b30, PreviousVersions: HLVVersions{srcA: aVal}}
	err = p4ApplyISGRRev(ctx, collection, docB, Body{}, true, bTb3, []string{"4-c3", "3-b2", "2-a1", rev1}, nil)
	require.NoError(t, err)
	bBefore := p4Read(t, ctx, collection, docB)
	p4Log(t, "B before a4 push", bBefore)

	a4HLV := a4.hlv.Copy()
	t.Logf("IsInConflict(B=%s@%d pv=%v, a4=%s@%d pv=%v) = %v", bBefore.hlv.SourceID, bBefore.hlv.Version, bBefore.hlv.PreviousVersions,
		a4HLV.SourceID, a4HLV.Version, a4HLV.PreviousVersions, IsInConflict(ctx, &bBefore.hlv, a4HLV))

	// passive sgr2 handler: no resolver, a4 is live so ForceAllowConflictingTombstone is false
	pushDoc := CreateTestDocument(docB, a4History[0], Body{"v": "a4"}, false, 0)
	_, _, _, err = collection.PutExistingCurrentVersion(ctx, PutDocOptions{
		NewDoc:         pushDoc,
		RevTreeHistory: a4History,
		NewDocHLV:      a4.hlv.Copy(),
		ISGRWrite:      true,
	})
	t.Logf("a4 push to B err=%v", err)
	bAfter := p4Read(t, ctx, collection, docB)
	p4Log(t, "B after a4 push", bAfter)
	status, _ := base.ErrorAsHTTPStatus(err)
	assert.Equal(t, http.StatusConflict, status, "claim: B rejects the a4 push with 409")
	assert.True(t, bAfter.deleted, "claim: B stays deleted")
}

// TestP4ISGRStaleTombstoneGated: same as above, but ForceAllowConflictingTombstone false, so IsInConflict runs.
func TestP4ISGRStaleTombstoneGated(t *testing.T) {
	db, ctx, collection, resolver := p4Setup(t)
	defer db.Close(ctx)
	const docID = "p4gated"

	rev1, _, err := collection.Put(ctx, docID, Body{"v": "x0"})
	require.NoError(t, err)
	x0 := p4Read(t, ctx, collection, docID)
	srcA, aVal := x0.hlv.SourceID, x0.hlv.Version
	b10, b30 := aVal+10, aVal+30

	tb3HLV := &HybridLogicalVector{SourceID: p4SrcB, Version: b30, PreviousVersions: HLVVersions{srcA: aVal}}
	require.NoError(t, p4ApplyISGRRev(ctx, collection, docID, Body{}, true, tb3HLV, []string{"4-c3", "3-b2", "2-a1", rev1}, resolver))
	afterTb3 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after tb3", afterTb3)

	tb1HLV := &HybridLogicalVector{SourceID: p4SrcB, Version: b10, PreviousVersions: HLVVersions{srcA: aVal}}
	_, _, _, err = collection.PutExistingCurrentVersion(ctx, PutDocOptions{
		NewDoc:           CreateTestDocument(docID, "2-a1", Body{}, true, 0),
		RevTreeHistory:   []string{"2-a1", rev1},
		NewDocHLV:        tb1HLV,
		ConflictResolver: resolver,
		ISGRWrite:        true,
	})
	t.Logf("tb1 (force=false) write err=%v", err)
	afterTb1 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after tb1 (force=false)", afterTb1)
	assert.Equal(t, b30, afterTb1.hlv.Version, "with the gate, cv stays srcB:b30")
}

// TestP4ISGRTombstonesInOrderControl: x0, tb1, then tb3, in order. Expect cv srcB:b30.
func TestP4ISGRTombstonesInOrderControl(t *testing.T) {
	db, ctx, collection, resolver := p4Setup(t)
	defer db.Close(ctx)
	const docID = "p4control"

	rev1, _, err := collection.Put(ctx, docID, Body{"v": "x0"})
	require.NoError(t, err)
	x0 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after x0 (local write)", x0)
	srcA, aVal := x0.hlv.SourceID, x0.hlv.Version
	b10, b30 := aVal+10, aVal+30

	tb1HLV := &HybridLogicalVector{SourceID: p4SrcB, Version: b10, PreviousVersions: HLVVersions{srcA: aVal}}
	err = p4ApplyISGRRev(ctx, collection, docID, Body{}, true, tb1HLV, []string{"2-a1", rev1}, resolver)
	t.Logf("tb1 write err=%v", err)
	require.NoError(t, err)
	p4Log(t, "after tb1", p4Read(t, ctx, collection, docID))

	tb3HLV := &HybridLogicalVector{SourceID: p4SrcB, Version: b30, PreviousVersions: HLVVersions{srcA: aVal}}
	err = p4ApplyISGRRev(ctx, collection, docID, Body{}, true, tb3HLV, []string{"4-c3", "3-b2", "2-a1", rev1}, resolver)
	t.Logf("tb3 write err=%v", err)
	require.NoError(t, err)
	afterTb3 := p4Read(t, ctx, collection, docID)
	p4Log(t, "after tb3", afterTb3)
	assert.Equal(t, p4SrcB, afterTb3.hlv.SourceID)
	assert.Equal(t, b30, afterTb3.hlv.Version, "control: cv is srcB:b30")
	assert.Equal(t, "4-c3", afterTb3.winner)
	assert.True(t, afterTb3.deleted)
}
