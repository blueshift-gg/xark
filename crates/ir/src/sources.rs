//! `sources.json`: the source line each constraint came from, compactly.
//!
//! Every `xark build` writes it beside `circuit.xbc` (which it never changes), so a
//! failing constraint can be reported as the statement that emitted it:
//!
//! ```text
//! src/lib.rs:77:20  id.nationality.require_one_of(allowed);
//! ```
//!
//! Constraints come in long runs from one statement, so the map is a list of
//! distinct [`Site`]s and the runs of constraint indices that map to each: a few
//! dozen entries for a small circuit, ~65k for a 1.6M-constraint ECDSA verifier.
//! `xark prove`, the Rust test harness and xark-wasm all read it through
//! [`SourceMap::at`]. (`profile.json`, from `xark profile`, is the full
//! per-constraint record behind `xark profile`'s cost breakdown.)

use serde::{Deserialize, Serialize};

/// Where a run of constraints came from.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Site {
    /// The circuit-crate source file of the top-level statement (`src/lib.rs`).
    pub file: String,
    /// 1-based line.
    pub line: u32,
    /// 1-based column.
    pub col: u32,
    /// The statement's source line, trimmed (filled in at build time, so a reader
    /// without the source, such as a browser, can still show it).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub text: String,
    /// The functions the statement called into, outermost first.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub chain: Vec<String>,
}

impl Site {
    /// `src/lib.rs:77:20`.
    pub fn location(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.col)
    }

    /// One line for an error: the location, the statement, and the function it
    /// failed in when that isn't the statement itself.
    pub fn describe(&self) -> String {
        let mut s = self.location();
        if !self.text.is_empty() {
            s.push_str(&format!(": `{}`", self.text));
        }
        if let Some(f) = self
            .chain
            .last()
            .filter(|f| !self.text.contains(f.as_str()))
        {
            s.push_str(&format!(" (in `{f}`)"));
        }
        s
    }
}

/// The `sources.json` document.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceMap {
    pub version: u32,
    /// The distinct sites.
    pub sites: Vec<Site>,
    /// `[start, site, start, site, …]`: constraints from `start` up to the next
    /// run's `start` came from `sites[site]`. Starts ascend from 0.
    pub runs: Vec<u32>,
}

/// No site (a constraint with no source attribution).
pub const NO_SITE: u32 = u32::MAX;

impl SourceMap {
    /// The map for constraints whose sites are `row_sites` (an index into
    /// `sites` per constraint, or [`NO_SITE`]). Unused sites are dropped.
    pub fn new(row_sites: impl IntoIterator<Item = u32>, sites: &[Site]) -> SourceMap {
        let mut keep = vec![NO_SITE; sites.len()];
        let mut out = SourceMap {
            version: 1,
            ..SourceMap::default()
        };
        let mut prev = None;
        for (row, s) in row_sites.into_iter().enumerate() {
            if prev == Some(s) {
                continue;
            }
            prev = Some(s);
            let idx = match sites.get(s as usize) {
                Some(site) if !site.file.is_empty() => {
                    if keep[s as usize] == NO_SITE {
                        keep[s as usize] = out.sites.len() as u32;
                        out.sites.push(site.clone());
                    }
                    keep[s as usize]
                }
                _ => NO_SITE,
            };
            out.runs.extend([row as u32, idx]);
        }
        out
    }

    /// Fill each site's `text` from its source file under `root`.
    pub fn read_text(&mut self, root: &std::path::Path) {
        let mut files: std::collections::HashMap<String, Option<String>> = Default::default();
        for s in &mut self.sites {
            let src = files
                .entry(s.file.clone())
                .or_insert_with(|| std::fs::read_to_string(root.join(&s.file)).ok());
            if let Some(line) = src
                .as_deref()
                .and_then(|t| t.lines().nth(s.line as usize - 1))
            {
                s.text = line.trim().to_string();
            }
        }
    }

    /// Where constraint `row` came from.
    pub fn at(&self, row: usize) -> Option<&Site> {
        // The last run starting at or before `row`.
        let (mut lo, mut hi) = (0, self.runs.len() / 2);
        while lo < hi {
            let mid = (lo + hi) / 2;
            if self.runs[2 * mid] as usize <= row {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let i = lo.checked_sub(1)?;
        self.sites.get(self.runs[2 * i + 1] as usize)
    }

    /// Constraints per source line, costliest first, for a circuit of `rows`
    /// constraints. Each line is represented by its first site; unattributed
    /// constraints are left out.
    pub fn line_costs(&self, rows: usize) -> Vec<(&Site, usize)> {
        let mut by_line: std::collections::HashMap<(&str, u32), (usize, usize)> =
            Default::default();
        for (i, run) in self.runs.as_chunks::<2>().0.iter().enumerate() {
            let end = self.runs.get(2 * i + 2).map_or(rows, |&s| s as usize);
            let Some(site) = self.sites.get(run[1] as usize) else {
                continue;
            };
            let e = by_line
                .entry((&site.file, site.line))
                .or_insert((run[1] as usize, 0));
            e.1 += end.saturating_sub(run[0] as usize);
        }
        let mut out: Vec<(&Site, usize)> = by_line
            .into_values()
            .map(|(site, n)| (&self.sites[site], n))
            .collect();
        out.sort_by(|a, b| (b.1, &a.0.file, a.0.line).cmp(&(a.1, &b.0.file, b.0.line)));
        out
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string(self).expect("a SourceMap serializes")
    }

    pub fn from_json(s: &str) -> Result<SourceMap, serde_json::Error> {
        serde_json::from_str(s)
    }

    /// `sources.json` from a build directory, if there is one.
    pub fn load(dir: &std::path::Path) -> Option<SourceMap> {
        let text = std::fs::read_to_string(dir.join("sources.json")).ok()?;
        SourceMap::from_json(&text).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn site(line: u32) -> Site {
        Site {
            file: "src/lib.rs".into(),
            line,
            col: 5,
            ..Site::default()
        }
    }

    #[test]
    fn runs_map_rows_to_sites() {
        let sites = [site(1), site(2), site(3), Site::default()];
        // Rows: 0,1 ← site 1; 2 ← unattributed; 3,4 ← site 0; 5 ← site 1 again.
        let m = SourceMap::new([1, 1, 3, 0, 0, 1], &sites);
        assert_eq!(m.sites, [site(2), site(1)]); // site 3 unused, unattributed dropped
        assert_eq!(m.runs, [0, 0, 2, NO_SITE, 3, 1, 5, 0]);
        let line = |r| m.at(r).map(|s| s.line);
        assert_eq!(
            (0..7).map(line).collect::<Vec<_>>(),
            [Some(2), Some(2), None, Some(1), Some(1), Some(2), Some(2)]
        );
        assert_eq!(SourceMap::from_json(&m.to_json()).unwrap(), m);
    }

    #[test]
    fn costs_lines() {
        let mut other_col = site(2);
        other_col.col = 9;
        let sites = [site(1), site(2), other_col, Site::default()];
        // Rows 0..2 ← line 2; 2 ← unattributed; 3..5 ← line 1; 5..9 ← line 2 again,
        // from another column.
        let m = SourceMap::new([1, 1, 3, 0, 0, 2, 2, 2, 2], &sites);
        let costs: Vec<_> = m.line_costs(9).iter().map(|(s, n)| (s.line, *n)).collect();
        assert_eq!(costs, [(2, 6), (1, 2)]);
    }

    #[test]
    fn describes_the_statement() {
        let mut s = site(77);
        s.col = 20;
        s.text = "id.nationality.require_one_of(allowed);".into();
        s.chain = vec!["require_one_of".into()];
        assert_eq!(
            s.describe(),
            "src/lib.rs:77:20: `id.nationality.require_one_of(allowed);`"
        );
        s.chain = vec!["commitment".into(), "hash".into(), "sbox".into()];
        s.text = "require_eq(id.commitment(), commitment);".into();
        assert_eq!(
            s.describe(),
            "src/lib.rs:77:20: `require_eq(id.commitment(), commitment);` (in `sbox`)"
        );
    }
}
