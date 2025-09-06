
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub(crate) struct ParsedIntegerLiteral {
    pub(crate) raw_value: u64,
    pub(crate) bit_width: usize,
    pub(crate) is_signed: bool,
}

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

pub(crate) fn parse_integer_literal(raw_literal_string: &str) -> Option<ParsedIntegerLiteral> {
    let mut string_slice: &str = raw_literal_string;
    if string_slice.ends_with("i64") {
        string_slice = &string_slice[0..string_slice.len() - 3];
        let mut sign_multiplier = 1;
        if string_slice.starts_with('-') {
            string_slice = &string_slice[1..];
            sign_multiplier = -1;
        }
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            i64::from_str_radix(string_slice, 16).ok()
        } else {
            i64::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: (x * sign_multiplier) as u64, is_signed: true, bit_width: 64})
    } else if string_slice.ends_with("i32") {
        string_slice = &string_slice[0..string_slice.len() - 3];
        let mut sign_multiplier = 1;
        if string_slice.starts_with('-') {
            string_slice = &string_slice[1..];
            sign_multiplier = -1;
        }
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            i32::from_str_radix(string_slice, 16).ok()
        } else {
            i32::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: (x * sign_multiplier) as u64, is_signed: true, bit_width: 32})
    } else if string_slice.ends_with("i16") {
        string_slice = &string_slice[0..string_slice.len() - 3];
        let mut sign_multiplier = 1;
        if string_slice.starts_with('-') {
            string_slice = &string_slice[1..];
            sign_multiplier = -1;
        }
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            i16::from_str_radix(string_slice, 16).ok()
        } else {
            i16::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: (x * sign_multiplier) as u64, is_signed: true, bit_width: 16})
    } else if string_slice.ends_with("i8") {
        string_slice = &string_slice[0..string_slice.len() - 2];
        let mut sign_multiplier = 1;
        if string_slice.starts_with('-') {
            string_slice = &string_slice[1..];
            sign_multiplier = -1;
        }
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            i8::from_str_radix(string_slice, 16).ok()
        } else {
            i8::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: (x * sign_multiplier) as u64, is_signed: true, bit_width: 8})
    } else if string_slice.ends_with("u64") {
        string_slice = &string_slice[0..string_slice.len() - 3];
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            u64::from_str_radix(string_slice, 16).ok()
        } else {
            u64::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: x, is_signed: false, bit_width: 64})
    } else if string_slice.ends_with("u32") {
        string_slice = &string_slice[0..string_slice.len() - 3];
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            u32::from_str_radix(string_slice, 16).ok()
        } else {
            u32::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: x as u64, is_signed: false, bit_width: 32})
    } else if string_slice.ends_with("u16") {
        string_slice = &string_slice[0..string_slice.len() - 3];
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            u16::from_str_radix(string_slice, 16).ok()
        } else {
            u16::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: x as u64, is_signed: false, bit_width: 16})
    } else if string_slice.ends_with("u8") {
        string_slice = &string_slice[0..string_slice.len() - 2];
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            u8::from_str_radix(string_slice, 16).ok()
        } else {
            u8::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: x as u64, is_signed: false, bit_width: 8})
    } else {
        let mut sign_multiplier = 1;
        if string_slice.starts_with('-') {
            string_slice = &string_slice[1..];
            sign_multiplier = -1;
        }
        if string_slice.starts_with("0x") {
            string_slice = &string_slice[2..];
            i32::from_str_radix(string_slice, 16).ok()
        } else {
            i32::from_str_radix(string_slice, 10).ok()
        }.map(|x| ParsedIntegerLiteral {raw_value: (x * sign_multiplier) as u64, is_signed: true, bit_width: 32})
    }
}
