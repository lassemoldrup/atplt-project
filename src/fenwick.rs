use itertools::Itertools;

/// A generic minimum suffix Fenwick tree.
pub struct MinFenwickTree<T> {
    data: Vec<T>,
    values: Vec<T>,
}

impl<T> MinFenwickTree<T>
where
    T: Copy + Ord,
{
    /// Builds a minimum suffix Fenwick tree from the given sequence.
    pub fn build<I>(into_iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let values = into_iter.into_iter().collect_vec();
        let mut data = values.iter().rev().copied().collect_vec();
        for i in 0..data.len() {
            let j = i | (i + 1);
            if j < data.len() {
                data[j] = data[i].min(data[j]);
            }
        }

        Self { data, values }
    }

    /// Returns the value at index `i`.
    ///
    /// # Panics
    /// Panics if `i >= n`.
    pub fn get(&self, i: usize) -> T {
        self.values[i]
    }

    /// Returns the minimum value in the range `[i, n)`, where `n` is the length
    /// of the original sequence.
    ///
    /// # Panics
    /// Panics if `i >= n`.
    pub fn query(&self, i: usize) -> T {
        let mut i = self.data.len() - i;
        let mut res = self.data[i - 1];
        i &= i - 1;

        while i > 0 {
            res = self.data[i - 1].min(res);
            i &= i - 1;
        }
        res
    }

    /// Updates the value at index `i` to `val`. `val` must be less than the
    /// current value.
    ///
    /// # Panics
    /// Panics if `i >= n` or `val` is greater than the current value at index
    /// `i`.
    pub fn update(&mut self, i: usize, val: T) {
        assert!(self.values[i] >= val);
        self.values[i] = val;
        let mut i = self.data.len() - i - 1;
        while i < self.data.len() {
            self.data[i] = self.data[i].min(val);
            i |= i + 1;
        }
    }

    /// Returns the largest index of a value less than or equal to `val`, or
    /// `None` if no such value exists.
    pub fn arg_leq(&self, val: T) -> Option<usize> {
        let n = self.data.len();

        let mut i = 0;
        let mut pw = n.next_power_of_two();
        while pw > 0 {
            let j = i + pw - 1;
            if j < n && self.data[j] > val {
                i += pw;
            }
            pw >>= 1;
        }

        (n - i).checked_sub(1)
    }
}

#[cfg(test)]
mod test {
    use super::MinFenwickTree;

    #[test]
    fn query_test() {
        let tree = MinFenwickTree::build([3, 2, 4, 10, 9]);
        assert_eq!(tree.query(0), 2);
        assert_eq!(tree.query(1), 2);
        assert_eq!(tree.query(2), 4);
        assert_eq!(tree.query(3), 9);
        assert_eq!(tree.query(4), 9);
    }

    #[test]
    fn update_test() {
        let mut tree = MinFenwickTree::build([3, 2, 4, 10, 9]);
        tree.update(3, 8);
        assert_eq!(tree.query(0), 2);
        assert_eq!(tree.query(1), 2);
        assert_eq!(tree.query(2), 4);
        assert_eq!(tree.query(3), 8);
        assert_eq!(tree.query(4), 9);
        tree.update(2, 1);
        assert_eq!(tree.query(0), 1);
        assert_eq!(tree.query(1), 1);
        assert_eq!(tree.query(2), 1);
        assert_eq!(tree.query(3), 8);
        assert_eq!(tree.query(4), 9);
    }

    #[test]
    fn arg_leq_test() {
        let tree = MinFenwickTree::build([3, 2, 4, 10, 9, 1, 5]);
        assert_eq!(tree.arg_leq(1), Some(5));
        let tree = MinFenwickTree::build([3, 2, 4, 10, 9, 11, 5, 7]);
        assert_eq!(tree.arg_leq(6), Some(6));
        assert_eq!(tree.arg_leq(4), Some(2));
        assert_eq!(tree.arg_leq(1), None);
    }
}
