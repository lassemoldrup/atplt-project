use std::collections::VecDeque;

pub trait Linearizations: Iterator
where
    Self::Item: IntoIterator,
{
    /// Returns an iterator over all linearizations of the subsequences.
    ///
    /// # Example
    /// ```
    /// let subsequences = vec![vec![1, 2], vec![3, 4]];
    /// let mut linearizations = subsequences.into_iter().linearizations();
    /// assert_eq!(linearizations.next(), Some(vec![1, 2, 3, 4]));
    /// assert_eq!(linearizations.next(), Some(vec![1, 3, 2, 4]));
    /// assert_eq!(linearizations.next(), Some(vec![1, 3, 4, 2]));
    /// assert_eq!(linearizations.next(), Some(vec![3, 1, 2, 4]));
    /// assert_eq!(linearizations.next(), Some(vec![3, 1, 4, 2]));
    /// assert_eq!(linearizations.next(), Some(vec![3, 4, 1, 2]));
    /// assert_eq!(linearizations.next(), None);
    /// ```
    fn linearizations(self) -> LinearizationsIter<<Self::Item as IntoIterator>::Item>;
}

impl<T> Linearizations for T
where
    T: Iterator,
    T::Item: IntoIterator,
{
    fn linearizations(self) -> LinearizationsIter<<Self::Item as IntoIterator>::Item> {
        let subsequences: Vec<VecDeque<_>> = self.map(|it| it.into_iter().collect()).collect();
        LinearizationsIter {
            total: subsequences.iter().map(|s| s.len()).sum(),
            subsequences,
            sequence: Vec::new(),
            stack: vec![None],
        }
    }
}

#[derive(Clone)]
pub struct LinearizationsIter<T> {
    total: usize,
    subsequences: Vec<VecDeque<T>>,
    sequence: Vec<T>,
    stack: Vec<Option<usize>>,
}
impl<T: Clone> Iterator for LinearizationsIter<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(frame) = self.stack.pop() {
            if frame.is_none() && self.sequence.len() == self.total {
                return Some(self.sequence.clone());
            }

            let mut k = if let Some(k) = frame {
                let x = self.sequence.pop().unwrap();
                self.subsequences[k].push_front(x);
                k + 1
            } else {
                0
            };

            while k < self.subsequences.len() {
                if let Some(x) = self.subsequences[k].pop_front() {
                    self.sequence.push(x);
                    // Backtracking
                    self.stack.push(Some(k));
                    // Call recursively
                    self.stack.push(None);
                    break;
                } else {
                    k += 1;
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use super::*;

    #[test]
    fn linearizations_two_subsequences_test() {
        let subsequences = vec![vec![1, 2], vec![3, 4]];
        let mut linearizations = subsequences.into_iter().linearizations();
        assert_eq!(linearizations.next(), Some(vec![1, 2, 3, 4]));
        assert_eq!(linearizations.next(), Some(vec![1, 3, 2, 4]));
        assert_eq!(linearizations.next(), Some(vec![1, 3, 4, 2]));
        assert_eq!(linearizations.next(), Some(vec![3, 1, 2, 4]));
        assert_eq!(linearizations.next(), Some(vec![3, 1, 4, 2]));
        assert_eq!(linearizations.next(), Some(vec![3, 4, 1, 2]));
        assert_eq!(linearizations.next(), None);
    }

    #[test]
    fn linearizations_three_subsequences_test() {
        let subsequences = vec![vec![1, 2], vec![3, 4], vec![5, 6]];
        let mut linearizations = subsequences.into_iter().linearizations();
        assert_eq!(linearizations.next(), Some(vec![1, 2, 3, 4, 5, 6]));
        assert_eq!(linearizations.next(), Some(vec![1, 2, 3, 5, 4, 6]));
        assert_eq!(linearizations.next(), Some(vec![1, 2, 3, 5, 6, 4]));
        assert_eq!(linearizations.next(), Some(vec![1, 2, 5, 3, 4, 6]));
        assert_eq!(linearizations.next(), Some(vec![1, 2, 5, 3, 6, 4]));
        assert_eq!(linearizations.next(), Some(vec![1, 2, 5, 6, 3, 4]));
        assert_eq!(linearizations.next(), Some(vec![1, 3, 2, 4, 5, 6]));
        for lin in linearizations {
            let pos = |x| lin.iter().find_position(|&&y| y == x).unwrap();
            assert!(pos(1) < pos(2));
            assert!(pos(3) < pos(4));
            assert!(pos(5) < pos(6));
        }
    }

    #[test]
    fn linearizations_edge_cases() {
        let subsequences = vec![vec![], vec![1, 2], vec![]];
        let mut linearizations = subsequences.into_iter().linearizations();
        assert_eq!(linearizations.next(), Some(vec![1, 2]));
        assert_eq!(linearizations.next(), None);

        let subsequences: Vec<Vec<usize>> = vec![vec![], vec![]];
        let mut linearizations = subsequences.into_iter().linearizations();
        assert_eq!(linearizations.next(), Some(vec![]));
        assert_eq!(linearizations.next(), None);

        let subsequences: Vec<Vec<usize>> = vec![];
        let mut linearizations = subsequences.into_iter().linearizations();
        assert_eq!(linearizations.next(), Some(vec![]));
        assert_eq!(linearizations.next(), None);
    }
}
