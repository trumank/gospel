
pub(crate) fn get_line_number_and_offset_from_index(contents: &str, char_index: usize) -> (usize, usize) {
    let mut current_index: usize = 0;
    let mut current_line_number: usize = 0;
    let mut current_line_start_index: usize = 0;

    while current_index < contents.len() && current_index <= char_index {
        if contents.as_bytes()[current_index] == '\n' as u8 {
            current_line_start_index = current_index;
            current_line_number += 1;
        }
        current_index += 1;
    }
    (current_line_number, char_index - current_line_start_index)
}

