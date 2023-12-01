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
    fn linearizations(
        self,
    ) -> LinearizationsIter<<Self::Item as IntoIterator>::Item, fn(usize, usize, usize) -> usize>;

    /// Returns an iterator over all linearizations of the subsequences given a
    /// constraint function `constraint_fn` that takes the index of a
    /// subsequence, the index of an element in that subsequence, and the
    /// index of another subsequence, and returns an index in that other
    /// subsequence that must come after the element in the first
    /// subsequence.
    ///
    /// # Example
    /// ```
    /// let subsequences = vec![vec![1, 2], vec![3, 4]];
    /// let mut linearizations = subsequences.into_iter().linearizations_with(|k1, i, k2| {
    ///     // 1 must come before 4
    ///     if k1 == 0 && k2 == 1 && i == 0 {
    ///         1
    ///     } else {
    ///         usize::MAX
    ///     }
    /// });
    /// assert_eq!(linearizations.next(), Some(vec![1, 2, 3, 4]));
    /// assert_eq!(linearizations.next(), Some(vec![1, 3, 2, 4]));
    /// assert_eq!(linearizations.next(), Some(vec![1, 3, 4, 2]));
    /// assert_eq!(linearizations.next(), Some(vec![3, 1, 2, 4]));
    /// assert_eq!(linearizations.next(), Some(vec![3, 1, 4, 2]));
    /// assert_eq!(linearizations.next(), None);
    fn linearizations_with<F>(
        self,
        constraint_fn: F,
    ) -> LinearizationsIter<<Self::Item as IntoIterator>::Item, F>
    where
        F: Fn(usize, usize, usize) -> usize;
}

impl<T> Linearizations for T
where
    T: Iterator,
    T::Item: IntoIterator,
{
    fn linearizations(
        self,
    ) -> LinearizationsIter<<Self::Item as IntoIterator>::Item, fn(usize, usize, usize) -> usize>
    {
        self.linearizations_with(|_, _, _| usize::MAX)
    }

    fn linearizations_with<F>(
        self,
        constraint_fn: F,
    ) -> LinearizationsIter<<Self::Item as IntoIterator>::Item, F>
    where
        F: Fn(usize, usize, usize) -> usize,
    {
        let subsequences: Vec<Vec<_>> = self.map(|it| it.into_iter().collect()).collect();
        LinearizationsIter {
            total: subsequences.iter().map(|s| s.len()).sum(),
            next_value: vec![0; subsequences.len()],
            subsequences,
            sequence: Vec::new(),
            stack: vec![None],
            constraint_fn,
        }
    }
}

#[derive(Clone)]
pub struct LinearizationsIter<T, F> {
    total: usize,
    subsequences: Vec<Vec<T>>,
    next_value: Vec<usize>,
    sequence: Vec<T>,
    stack: Vec<Option<usize>>,
    constraint_fn: F,
}

impl<T, F> Iterator for LinearizationsIter<T, F>
where
    T: Clone,
    F: Fn(usize, usize, usize) -> usize,
{
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(frame) = self.stack.pop() {
            if frame.is_none() && self.sequence.len() == self.total {
                return Some(self.sequence.clone());
            }

            let start_k = if let Some(k) = frame {
                self.sequence.pop();
                self.next_value[k] -= 1;
                k + 1
            } else {
                0
            };

            'subseq: for k in start_k..self.subsequences.len() {
                let sub_idx = self.next_value[k];
                let Some(x) = self.subsequences[k].get(sub_idx) else {
                    continue;
                };

                // Check constraints
                // TODO: Maybe optimize this for naive constraints
                for k2 in 0..self.subsequences.len() {
                    if (self.constraint_fn)(k, sub_idx, k2) < self.next_value[k2] {
                        continue 'subseq;
                    }
                }

                self.next_value[k] += 1;
                self.sequence.push(x.clone());
                // Backtracking
                self.stack.push(Some(k));
                // Call recursively
                self.stack.push(None);
                break;
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

    #[test]
    fn linearizations_with_test() {
        let subsequences = vec![vec![1, 2], vec![3, 4]];
        let mut linearizations = subsequences.into_iter().linearizations_with(|k1, i, k2| {
            if k1 == 0 && k2 == 1 && i == 0 {
                // 1 must come before 4
                1
            } else if k1 == 1 && k2 == 0 && i == 0 {
                // 3 must come before 2
                1
            } else {
                usize::MAX
            }
        });
        assert_eq!(linearizations.next(), Some(vec![1, 3, 2, 4]));
        assert_eq!(linearizations.next(), Some(vec![1, 3, 4, 2]));
        assert_eq!(linearizations.next(), Some(vec![3, 1, 2, 4]));
        assert_eq!(linearizations.next(), Some(vec![3, 1, 4, 2]));
        assert_eq!(linearizations.next(), None);
    }
}
