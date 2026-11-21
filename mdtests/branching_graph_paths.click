spec enum Path {
    Here,
    Left(Path),
    Right(Path),
}

function walk(left: int32[], right: int32[], from: int32, path: Path) -> int32
    decreases path
{
    match path {
        Path::Here => from,
        Path::Left(rest) => walk(left, right, left[from], rest),
        Path::Right(rest) => walk(left, right, right[from], rest),
    }
}

theorem left_path(left: int32[], right: int32[], from: int32, rest: Path) {
    ensures walk(left, right, from, Path::Left(rest))
        == walk(left, right, left[from], rest) by {
        unfold(walk(left, right, from, Path::Left(rest)));
        known();
    }
}

theorem right_path(left: int32[], right: int32[], from: int32, rest: Path) {
    ensures walk(left, right, from, Path::Right(rest))
        == walk(left, right, right[from], rest) by {
        unfold(walk(left, right, from, Path::Right(rest)));
        known();
    }
}

theorem prepend_left(left: int32[], right: int32[], from: int32, to: int32) {
    requires exists (path: Path) {
        walk(left, right, left[from], path) == to
    };
    ensures exists (path: Path) { walk(left, right, from, path) == to } by {
        let rest = obtain(exists (rest: Path) {
            walk(left, right, left[from], rest) == to
        });
        witness(Path::Left(rest));
        unfold(walk(left, right, from, Path::Left(rest)));
        known();
    }
}

theorem prepend_right(left: int32[], right: int32[], from: int32, to: int32) {
    requires exists (path: Path) {
        walk(left, right, right[from], path) == to
    };
    ensures exists (path: Path) { walk(left, right, from, path) == to } by {
        let rest = obtain(exists (rest: Path) {
            walk(left, right, right[from], rest) == to
        });
        witness(Path::Right(rest));
        unfold(walk(left, right, from, Path::Right(rest)));
        known();
    }
}

theorem walk_frame(a: int32[], b: int32[], c: int32[], d: int32[], n: int32, from: int32, path: Path) {
    requires 0 <= from;
    requires from < n;
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= a[k] and a[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= b[k] and b[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies a[k] == c[k] };
    requires forall (k: int32) { 0 <= k and k < n implies b[k] == d[k] };
    ensures walk(a, b, from, path) == walk(c, d, from, path) by {
        let ih = induct(path);
        match path {
            Path::Here => {
                unfold(walk(a, b, from, Path::Here));
                unfold(walk(c, d, from, Path::Here));
                known();
            }
            Path::Left(rest) => {
                have 0 <= a[from] and a[from] < n by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= a[k] and a[k] < n }, from);
                    known();
                }
                have a[from] == c[from] by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies a[k] == c[k] }, from);
                    known();
                }
                apply(ih(a, b, c, d, n, a[from], rest));
                unfold(walk(a, b, from, Path::Left(rest)));
                unfold(walk(c, d, from, Path::Left(rest)));
                solve() using {
                    a[from] == c[from];
                    walk(a, b, a[from], rest) == walk(c, d, a[from], rest);
                };
            }
            Path::Right(rest) => {
                have 0 <= b[from] and b[from] < n by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= b[k] and b[k] < n }, from);
                    known();
                }
                have b[from] == d[from] by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies b[k] == d[k] }, from);
                    known();
                }
                apply(ih(a, b, c, d, n, b[from], rest));
                unfold(walk(a, b, from, Path::Right(rest)));
                unfold(walk(c, d, from, Path::Right(rest)));
                solve() using {
                    b[from] == d[from];
                    walk(a, b, b[from], rest) == walk(c, d, b[from], rest);
                };
            }
        }
    }
}
theorem closed_marks_exclude_target(left: int32[], right: int32[], v: int32[], n: int32, from: int32, to: int32, path: Path) {
    requires 0 <= from;
    requires from < n;
    requires v[from] != 0;
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= right[k] and right[k] < n };
    requires forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) };
    ensures walk(left, right, from, path) != to by {
        let ih = induct(path);
        match path {
            Path::Here => {
                instantiate(forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) }, from);
                have from != to;
                unfold(walk(left, right, from, Path::Here));
                known();
            }
            Path::Left(rest) => {
                instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n }, from);
                have 0 <= left[from]; have left[from] < n;
                instantiate(forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) }, from);
                have v[left[from]] != 0;
                apply(ih(left, right, v, n, left[from], to, rest));
                unfold(walk(left, right, from, Path::Left(rest)));
                known();
            }
            Path::Right(rest) => {
                instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= right[k] and right[k] < n }, from);
                have 0 <= right[from]; have right[from] < n;
                instantiate(forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) }, from);
                have v[right[from]] != 0;
                apply(ih(left, right, v, n, right[from], to, rest));
                unfold(walk(left, right, from, Path::Right(rest)));
                known();
            }
        }
    }
}

theorem exhausted_zero_entry(left: int32[], right: int32[], before: int32[], after: int32[], n: int32, from: int32, to: int32) {
    requires 0 <= from;
    requires from < n;
    requires after[from] != 0;
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= right[k] and right[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies before[k] == 0 };
    requires forall (k: int32) { 0 <= k and k < n and before[k] == 0 and after[k] != 0 implies after[left[k]] != 0 and after[right[k]] != 0 };
    requires 0 <= to and to < n implies after[to] == before[to];
    ensures forall (path: Path) { walk(left, right, from, path) != to } by {
        have forall (k: int32) { 0 <= k and k < n and after[k] != 0 implies k != to and (after[left[k]] != 0 and after[right[k]] != 0) } by {
            intro(); intro();
            have 0 <= k; have k < n; have after[k] != 0;
            instantiate(forall (k: int32) { 0 <= k and k < n implies before[k] == 0 }, k);
            instantiate(forall (k: int32) { 0 <= k and k < n and before[k] == 0 and after[k] != 0 implies after[left[k]] != 0 and after[right[k]] != 0 }, k);
            have k != to by {
                if k == to {
                    have 0 <= to;
                    have to < n;
                    have 0 <= to and to < n by known();
                    have after[to] == before[to];
                    have before[to] == 0 by {
                        instantiate(forall (k: int32) { 0 <= k and k < n implies before[k] == 0 }, to);
                        known();
                    }
                    have after[to] == 0 by { rewrite(after[to], before[to]); known(); }
                    have after[k] == 0 by { rewrite(k, to); known(); }
                    contradiction(after[k] != 0);
                } else { known(); }
            }
            known();
        }
        intro();
        apply(closed_marks_exclude_target(left, right, after, n, from, to, path));
        known();
    }
}
