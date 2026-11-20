use crate::persistent::PersistentMap;

/// A persistent set of excluded integers stored as disjoint, nonadjacent
/// inclusive runs. A fork shares its parent's runs until it inserts a value.
#[derive(Clone, Debug, Default)]
pub(super) struct ExcludedIntegers {
    runs: PersistentMap<i128, i128>,
}

impl ExcludedIntegers {
    pub(super) fn containing(&self, value: i128) -> Option<(i128, i128)> {
        self.run_at_or_below(value).filter(|(_, end)| *end >= value)
    }

    pub(super) fn insert(&mut self, value: i128) {
        let mut start = value;
        let mut end = value;
        if let Some((left, left_end)) = self.run_at_or_below(value) {
            if left_end >= value {
                return;
            }
            if left_end.checked_add(1) == Some(value) {
                start = left;
                self.runs = self.runs.without_key(&left);
            }
        }
        if let Some(right) = value.checked_add(1)
            && let Some(&right_end) = self.runs.get(&right)
        {
            end = right_end;
            self.runs = self.runs.without_key(&right);
        }
        self.runs.insert(start, end);
    }

    fn run_at_or_below(&self, value: i128) -> Option<(i128, i128)> {
        self.runs
            .get_key_value(&value)
            .or_else(|| self.runs.get_less_than(&value))
            .map(|(&start, &end)| (start, end))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insertion_bridges_runs_without_filling_gaps_or_wrapping() {
        let mut excluded = ExcludedIntegers::default();
        for value in [i128::MIN, i128::MAX, 0, 2, 3, 1, 2, 5] {
            excluded.insert(value);
        }
        assert_eq!(excluded.containing(2), Some((0, 3)));
        assert_eq!(excluded.containing(4), None);
        assert_eq!(excluded.containing(5), Some((5, 5)));
        assert_eq!(excluded.containing(i128::MIN), Some((i128::MIN, i128::MIN)));
        assert_eq!(excluded.containing(i128::MAX), Some((i128::MAX, i128::MAX)));

        excluded.insert(i128::MIN + 1);
        excluded.insert(i128::MAX - 1);
        assert_eq!(
            excluded.containing(i128::MIN + 1),
            Some((i128::MIN, i128::MIN + 1))
        );
        assert_eq!(
            excluded.containing(i128::MAX),
            Some((i128::MAX - 1, i128::MAX))
        );
    }
}
