pub fn tag_size(variant_count: usize) -> usize {
    variant_count.next_power_of_two().ilog2() as usize
}
