//! Immutable evaluated sequence elements. Native inputs and selected native
//! readings stay explicit; produced values retain their existing common roots.
use super::*;
use crate::kernel::{ExecutionValue, RetainedProgramValue};

#[derive(Clone)]
pub struct SequenceValues(Arc<SequenceValuesStorage>);
enum SequenceValuesStorage {
    Input(Arc<[ProgramValue]>),
    Retained(Box<[RetainedProgramValue]>),
}
impl SequenceValues {
    pub fn len(&self) -> usize {
        match self.0.as_ref() {
            SequenceValuesStorage::Input(values) => values.len(),
            SequenceValuesStorage::Retained(values) => values.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// The selected native compatibility reading, without exporting other elements.
    pub fn get(&self, index: usize) -> Option<&ProgramValue> {
        match self.0.as_ref() {
            SequenceValuesStorage::Input(values) => values.get(index),
            SequenceValuesStorage::Retained(values) => {
                values.get(index).map(RetainedProgramValue::native_compat)
            }
        }
    }
    pub fn iter(&self) -> SequenceValuesIter<'_> {
        SequenceValuesIter {
            values: self,
            range: 0..self.len(),
        }
    }
    #[cfg(test)]
    pub(crate) fn retained_value(&self, index: usize) -> Option<ExecutionValue> {
        match self.0.as_ref() {
            SequenceValuesStorage::Input(values) => {
                values.get(index).cloned().map(ExecutionValue::Native)
            }
            SequenceValuesStorage::Retained(values) => values
                .get(index)
                .cloned()
                .map(RetainedProgramValue::into_value),
        }
    }
    pub(crate) fn retained_value_ref(&self, index: usize) -> Option<&ExecutionValue> {
        match self.0.as_ref() {
            SequenceValuesStorage::Input(_) => None,
            SequenceValuesStorage::Retained(values) => {
                values.get(index).map(RetainedProgramValue::value)
            }
        }
    }
    pub(crate) fn map_values(
        &self,
        mut native: impl FnMut(&ProgramValue) -> ProgramValue,
        mut retained: impl FnMut(&ExecutionValue) -> ExecutionValue,
    ) -> Self {
        match self.0.as_ref() {
            SequenceValuesStorage::Input(values) => {
                Self::from(values.iter().map(&mut native).collect::<Vec<_>>())
            }
            SequenceValuesStorage::Retained(values) => {
                Self::from_values(values.iter().map(|value| retained(value.value())))
            }
        }
    }
    pub(crate) fn from_values(values: impl IntoIterator<Item = ExecutionValue>) -> Self {
        Self(Arc::new(SequenceValuesStorage::Retained(
            values.into_iter().map(RetainedProgramValue::from).collect(),
        )))
    }
}
impl From<Arc<[ProgramValue]>> for SequenceValues {
    fn from(values: Arc<[ProgramValue]>) -> Self {
        Self(Arc::new(SequenceValuesStorage::Input(values)))
    }
}
impl From<Vec<ProgramValue>> for SequenceValues {
    fn from(values: Vec<ProgramValue>) -> Self {
        Self::from(Arc::<[ProgramValue]>::from(values))
    }
}
impl<const N: usize> From<[ProgramValue; N]> for SequenceValues {
    fn from(values: [ProgramValue; N]) -> Self {
        Self::from(Vec::from(values))
    }
}
impl FromIterator<ProgramValue> for SequenceValues {
    fn from_iter<I: IntoIterator<Item = ProgramValue>>(values: I) -> Self {
        Self::from(values.into_iter().collect::<Vec<_>>())
    }
}
impl PartialEq for SequenceValues {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.iter().eq(other.iter())
    }
}
impl Eq for SequenceValues {}
impl PartialOrd for SequenceValues {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SequenceValues {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}
impl Hash for SequenceValues {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for value in self.iter() {
            value.hash(state);
        }
    }
}
impl std::fmt::Debug for SequenceValues {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_list().entries(self.iter()).finish()
    }
}
pub struct SequenceValuesIter<'a> {
    values: &'a SequenceValues,
    range: std::ops::Range<usize>,
}
impl<'a> Iterator for SequenceValuesIter<'a> {
    type Item = &'a ProgramValue;
    fn next(&mut self) -> Option<Self::Item> {
        self.range.next().and_then(|index| self.values.get(index))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}
impl DoubleEndedIterator for SequenceValuesIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range
            .next_back()
            .and_then(|index| self.values.get(index))
    }
}
impl ExactSizeIterator for SequenceValuesIter<'_> {}
impl std::iter::FusedIterator for SequenceValuesIter<'_> {}
impl<'a> IntoIterator for &'a SequenceValues {
    type Item = &'a ProgramValue;
    type IntoIter = SequenceValuesIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
