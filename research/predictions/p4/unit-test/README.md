# P4 unit test (unscored)

A test run inside Couchbase Sync Gateway's own test framework (the `db` package, on its in-memory
rosmar backend), after P4 was committed and before the live runs. It is not part of P4's scored
Steps.

- `p4_tombstone_regression_test.go`: for `main` at `f1c59eb2`. `p4_tombstone_regression_test_412.go`:
  the same for tag `4.1.2` (`deb6c06b`), which has `setupTestDB` instead of `SetupTestDB`. Copy the
  file into `db/` of a Sync Gateway checkout and run `go test ./db -run 'TestP4' -count=1 -v`.
- It calls `PutExistingCurrentVersion` with the options `processRev` uses on the active pull side
  (`ISGRWrite`, `ForceAllowConflictingTombstone`, the default resolver): the newer tombstone (cv B+30)
  and then the older one (cv B+10).
- Result on both versions: the current version moves back to B+10 and B+30 leaves the HLV; the write
  is stored; the rev-tree winner stays the newer tombstone; a later local write on that document is
  rejected with 409 by a document holding the passive side's state. With
  `ForceAllowConflictingTombstone=false` the older tombstone is ignored; in order, the result is
  correct. Sync Gateway logs `Assertion failed: couldn't find channels for newRevID` on the stale
  write (on 4.1.2 the test harness fails the package run because of that assertion count; the three
  tests themselves pass).
- It does not test whether the out-of-order arrival happens in a real replication; the live runs in
  [../live/](../live/) do.
- Logs: `p4-main.log`, `p4-412.log`, `p4-main-devmode.log` (local paths shortened).
