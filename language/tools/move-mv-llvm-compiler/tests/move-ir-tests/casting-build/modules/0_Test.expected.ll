; ModuleID = '0x100__Test'
source_filename = "<unknown>"

define i128 @Test__cast_u128_as_u128(i128 %0) {
entry:
  %local_0 = alloca i128, align 8
  %local_1 = alloca i128, align 8
  %local_2 = alloca i128, align 8
  store i128 %0, ptr %local_0, align 4
  %load_store_tmp = load i128, ptr %local_0, align 4
  store i128 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i128, ptr %local_1, align 4
  store i128 %cast_src, ptr %local_2, align 4
  %retval = load i128, ptr %local_2, align 4
  ret i128 %retval
}

define i16 @Test__cast_u128_as_u16(i128 %0) {
entry:
  %local_0 = alloca i128, align 8
  %local_1 = alloca i128, align 8
  %local_2 = alloca i16, align 2
  store i128 %0, ptr %local_0, align 4
  %load_store_tmp = load i128, ptr %local_0, align 4
  store i128 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i128, ptr %local_1, align 4
  %trunc_dst = trunc i128 %cast_src to i16
  store i16 %trunc_dst, ptr %local_2, align 2
  %retval = load i16, ptr %local_2, align 2
  ret i16 %retval
}

define i256 @Test__cast_u128_as_u256(i128 %0) {
entry:
  %local_0 = alloca i128, align 8
  %local_1 = alloca i128, align 8
  %local_2 = alloca i256, align 8
  store i128 %0, ptr %local_0, align 4
  %load_store_tmp = load i128, ptr %local_0, align 4
  store i128 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i128, ptr %local_1, align 4
  %zext_dst = zext i128 %cast_src to i256
  store i256 %zext_dst, ptr %local_2, align 4
  %retval = load i256, ptr %local_2, align 4
  ret i256 %retval
}

define i32 @Test__cast_u128_as_u32(i128 %0) {
entry:
  %local_0 = alloca i128, align 8
  %local_1 = alloca i128, align 8
  %local_2 = alloca i32, align 4
  store i128 %0, ptr %local_0, align 4
  %load_store_tmp = load i128, ptr %local_0, align 4
  store i128 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i128, ptr %local_1, align 4
  %trunc_dst = trunc i128 %cast_src to i32
  store i32 %trunc_dst, ptr %local_2, align 4
  %retval = load i32, ptr %local_2, align 4
  ret i32 %retval
}

define i64 @Test__cast_u128_as_u64(i128 %0) {
entry:
  %local_0 = alloca i128, align 8
  %local_1 = alloca i128, align 8
  %local_2 = alloca i64, align 8
  store i128 %0, ptr %local_0, align 4
  %load_store_tmp = load i128, ptr %local_0, align 4
  store i128 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i128, ptr %local_1, align 4
  %trunc_dst = trunc i128 %cast_src to i64
  store i64 %trunc_dst, ptr %local_2, align 4
  %retval = load i64, ptr %local_2, align 4
  ret i64 %retval
}

define i8 @Test__cast_u128_as_u8(i128 %0) {
entry:
  %local_0 = alloca i128, align 8
  %local_1 = alloca i128, align 8
  %local_2 = alloca i8, align 1
  store i128 %0, ptr %local_0, align 4
  %load_store_tmp = load i128, ptr %local_0, align 4
  store i128 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i128, ptr %local_1, align 4
  %trunc_dst = trunc i128 %cast_src to i8
  store i8 %trunc_dst, ptr %local_2, align 1
  %retval = load i8, ptr %local_2, align 1
  ret i8 %retval
}

define i128 @Test__cast_u16_as_u128(i16 %0) {
entry:
  %local_0 = alloca i16, align 2
  %local_1 = alloca i16, align 2
  %local_2 = alloca i128, align 8
  store i16 %0, ptr %local_0, align 2
  %load_store_tmp = load i16, ptr %local_0, align 2
  store i16 %load_store_tmp, ptr %local_1, align 2
  %cast_src = load i16, ptr %local_1, align 2
  %zext_dst = zext i16 %cast_src to i128
  store i128 %zext_dst, ptr %local_2, align 4
  %retval = load i128, ptr %local_2, align 4
  ret i128 %retval
}

define i16 @Test__cast_u16_as_u16(i16 %0) {
entry:
  %local_0 = alloca i16, align 2
  %local_1 = alloca i16, align 2
  %local_2 = alloca i16, align 2
  store i16 %0, ptr %local_0, align 2
  %load_store_tmp = load i16, ptr %local_0, align 2
  store i16 %load_store_tmp, ptr %local_1, align 2
  %cast_src = load i16, ptr %local_1, align 2
  store i16 %cast_src, ptr %local_2, align 2
  %retval = load i16, ptr %local_2, align 2
  ret i16 %retval
}

define i256 @Test__cast_u16_as_u256(i16 %0) {
entry:
  %local_0 = alloca i16, align 2
  %local_1 = alloca i16, align 2
  %local_2 = alloca i256, align 8
  store i16 %0, ptr %local_0, align 2
  %load_store_tmp = load i16, ptr %local_0, align 2
  store i16 %load_store_tmp, ptr %local_1, align 2
  %cast_src = load i16, ptr %local_1, align 2
  %zext_dst = zext i16 %cast_src to i256
  store i256 %zext_dst, ptr %local_2, align 4
  %retval = load i256, ptr %local_2, align 4
  ret i256 %retval
}

define i32 @Test__cast_u16_as_u32(i16 %0) {
entry:
  %local_0 = alloca i16, align 2
  %local_1 = alloca i16, align 2
  %local_2 = alloca i32, align 4
  store i16 %0, ptr %local_0, align 2
  %load_store_tmp = load i16, ptr %local_0, align 2
  store i16 %load_store_tmp, ptr %local_1, align 2
  %cast_src = load i16, ptr %local_1, align 2
  %zext_dst = zext i16 %cast_src to i32
  store i32 %zext_dst, ptr %local_2, align 4
  %retval = load i32, ptr %local_2, align 4
  ret i32 %retval
}

define i64 @Test__cast_u16_as_u64(i16 %0) {
entry:
  %local_0 = alloca i16, align 2
  %local_1 = alloca i16, align 2
  %local_2 = alloca i64, align 8
  store i16 %0, ptr %local_0, align 2
  %load_store_tmp = load i16, ptr %local_0, align 2
  store i16 %load_store_tmp, ptr %local_1, align 2
  %cast_src = load i16, ptr %local_1, align 2
  %zext_dst = zext i16 %cast_src to i64
  store i64 %zext_dst, ptr %local_2, align 4
  %retval = load i64, ptr %local_2, align 4
  ret i64 %retval
}

define i8 @Test__cast_u16_as_u8(i16 %0) {
entry:
  %local_0 = alloca i16, align 2
  %local_1 = alloca i16, align 2
  %local_2 = alloca i8, align 1
  store i16 %0, ptr %local_0, align 2
  %load_store_tmp = load i16, ptr %local_0, align 2
  store i16 %load_store_tmp, ptr %local_1, align 2
  %cast_src = load i16, ptr %local_1, align 2
  %trunc_dst = trunc i16 %cast_src to i8
  store i8 %trunc_dst, ptr %local_2, align 1
  %retval = load i8, ptr %local_2, align 1
  ret i8 %retval
}

define i128 @Test__cast_u256_as_u128(i256 %0) {
entry:
  %local_0 = alloca i256, align 8
  %local_1 = alloca i256, align 8
  %local_2 = alloca i128, align 8
  store i256 %0, ptr %local_0, align 4
  %load_store_tmp = load i256, ptr %local_0, align 4
  store i256 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i256, ptr %local_1, align 4
  %trunc_dst = trunc i256 %cast_src to i128
  store i128 %trunc_dst, ptr %local_2, align 4
  %retval = load i128, ptr %local_2, align 4
  ret i128 %retval
}

define i16 @Test__cast_u256_as_u16(i256 %0) {
entry:
  %local_0 = alloca i256, align 8
  %local_1 = alloca i256, align 8
  %local_2 = alloca i16, align 2
  store i256 %0, ptr %local_0, align 4
  %load_store_tmp = load i256, ptr %local_0, align 4
  store i256 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i256, ptr %local_1, align 4
  %trunc_dst = trunc i256 %cast_src to i16
  store i16 %trunc_dst, ptr %local_2, align 2
  %retval = load i16, ptr %local_2, align 2
  ret i16 %retval
}

define i256 @Test__cast_u256_as_u256(i256 %0) {
entry:
  %local_0 = alloca i256, align 8
  %local_1 = alloca i256, align 8
  %local_2 = alloca i256, align 8
  store i256 %0, ptr %local_0, align 4
  %load_store_tmp = load i256, ptr %local_0, align 4
  store i256 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i256, ptr %local_1, align 4
  store i256 %cast_src, ptr %local_2, align 4
  %retval = load i256, ptr %local_2, align 4
  ret i256 %retval
}

define i32 @Test__cast_u256_as_u32(i256 %0) {
entry:
  %local_0 = alloca i256, align 8
  %local_1 = alloca i256, align 8
  %local_2 = alloca i32, align 4
  store i256 %0, ptr %local_0, align 4
  %load_store_tmp = load i256, ptr %local_0, align 4
  store i256 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i256, ptr %local_1, align 4
  %trunc_dst = trunc i256 %cast_src to i32
  store i32 %trunc_dst, ptr %local_2, align 4
  %retval = load i32, ptr %local_2, align 4
  ret i32 %retval
}

define i64 @Test__cast_u256_as_u64(i256 %0) {
entry:
  %local_0 = alloca i256, align 8
  %local_1 = alloca i256, align 8
  %local_2 = alloca i64, align 8
  store i256 %0, ptr %local_0, align 4
  %load_store_tmp = load i256, ptr %local_0, align 4
  store i256 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i256, ptr %local_1, align 4
  %trunc_dst = trunc i256 %cast_src to i64
  store i64 %trunc_dst, ptr %local_2, align 4
  %retval = load i64, ptr %local_2, align 4
  ret i64 %retval
}

define i8 @Test__cast_u256_as_u8(i256 %0) {
entry:
  %local_0 = alloca i256, align 8
  %local_1 = alloca i256, align 8
  %local_2 = alloca i8, align 1
  store i256 %0, ptr %local_0, align 4
  %load_store_tmp = load i256, ptr %local_0, align 4
  store i256 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i256, ptr %local_1, align 4
  %trunc_dst = trunc i256 %cast_src to i8
  store i8 %trunc_dst, ptr %local_2, align 1
  %retval = load i8, ptr %local_2, align 1
  ret i8 %retval
}

define i128 @Test__cast_u32_as_u128(i32 %0) {
entry:
  %local_0 = alloca i32, align 4
  %local_1 = alloca i32, align 4
  %local_2 = alloca i128, align 8
  store i32 %0, ptr %local_0, align 4
  %load_store_tmp = load i32, ptr %local_0, align 4
  store i32 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i32, ptr %local_1, align 4
  %zext_dst = zext i32 %cast_src to i128
  store i128 %zext_dst, ptr %local_2, align 4
  %retval = load i128, ptr %local_2, align 4
  ret i128 %retval
}

define i16 @Test__cast_u32_as_u16(i32 %0) {
entry:
  %local_0 = alloca i32, align 4
  %local_1 = alloca i32, align 4
  %local_2 = alloca i16, align 2
  store i32 %0, ptr %local_0, align 4
  %load_store_tmp = load i32, ptr %local_0, align 4
  store i32 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i32, ptr %local_1, align 4
  %trunc_dst = trunc i32 %cast_src to i16
  store i16 %trunc_dst, ptr %local_2, align 2
  %retval = load i16, ptr %local_2, align 2
  ret i16 %retval
}

define i256 @Test__cast_u32_as_u256(i32 %0) {
entry:
  %local_0 = alloca i32, align 4
  %local_1 = alloca i32, align 4
  %local_2 = alloca i256, align 8
  store i32 %0, ptr %local_0, align 4
  %load_store_tmp = load i32, ptr %local_0, align 4
  store i32 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i32, ptr %local_1, align 4
  %zext_dst = zext i32 %cast_src to i256
  store i256 %zext_dst, ptr %local_2, align 4
  %retval = load i256, ptr %local_2, align 4
  ret i256 %retval
}

define i32 @Test__cast_u32_as_u32(i32 %0) {
entry:
  %local_0 = alloca i32, align 4
  %local_1 = alloca i32, align 4
  %local_2 = alloca i32, align 4
  store i32 %0, ptr %local_0, align 4
  %load_store_tmp = load i32, ptr %local_0, align 4
  store i32 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i32, ptr %local_1, align 4
  store i32 %cast_src, ptr %local_2, align 4
  %retval = load i32, ptr %local_2, align 4
  ret i32 %retval
}

define i64 @Test__cast_u32_as_u64(i32 %0) {
entry:
  %local_0 = alloca i32, align 4
  %local_1 = alloca i32, align 4
  %local_2 = alloca i64, align 8
  store i32 %0, ptr %local_0, align 4
  %load_store_tmp = load i32, ptr %local_0, align 4
  store i32 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i32, ptr %local_1, align 4
  %zext_dst = zext i32 %cast_src to i64
  store i64 %zext_dst, ptr %local_2, align 4
  %retval = load i64, ptr %local_2, align 4
  ret i64 %retval
}

define i8 @Test__cast_u32_as_u8(i32 %0) {
entry:
  %local_0 = alloca i32, align 4
  %local_1 = alloca i32, align 4
  %local_2 = alloca i8, align 1
  store i32 %0, ptr %local_0, align 4
  %load_store_tmp = load i32, ptr %local_0, align 4
  store i32 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i32, ptr %local_1, align 4
  %trunc_dst = trunc i32 %cast_src to i8
  store i8 %trunc_dst, ptr %local_2, align 1
  %retval = load i8, ptr %local_2, align 1
  ret i8 %retval
}

define i128 @Test__cast_u64_as_u128(i64 %0) {
entry:
  %local_0 = alloca i64, align 8
  %local_1 = alloca i64, align 8
  %local_2 = alloca i128, align 8
  store i64 %0, ptr %local_0, align 4
  %load_store_tmp = load i64, ptr %local_0, align 4
  store i64 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i64, ptr %local_1, align 4
  %zext_dst = zext i64 %cast_src to i128
  store i128 %zext_dst, ptr %local_2, align 4
  %retval = load i128, ptr %local_2, align 4
  ret i128 %retval
}

define i16 @Test__cast_u64_as_u16(i64 %0) {
entry:
  %local_0 = alloca i64, align 8
  %local_1 = alloca i64, align 8
  %local_2 = alloca i16, align 2
  store i64 %0, ptr %local_0, align 4
  %load_store_tmp = load i64, ptr %local_0, align 4
  store i64 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i64, ptr %local_1, align 4
  %trunc_dst = trunc i64 %cast_src to i16
  store i16 %trunc_dst, ptr %local_2, align 2
  %retval = load i16, ptr %local_2, align 2
  ret i16 %retval
}

define i256 @Test__cast_u64_as_u256(i64 %0) {
entry:
  %local_0 = alloca i64, align 8
  %local_1 = alloca i64, align 8
  %local_2 = alloca i256, align 8
  store i64 %0, ptr %local_0, align 4
  %load_store_tmp = load i64, ptr %local_0, align 4
  store i64 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i64, ptr %local_1, align 4
  %zext_dst = zext i64 %cast_src to i256
  store i256 %zext_dst, ptr %local_2, align 4
  %retval = load i256, ptr %local_2, align 4
  ret i256 %retval
}

define i32 @Test__cast_u64_as_u32(i64 %0) {
entry:
  %local_0 = alloca i64, align 8
  %local_1 = alloca i64, align 8
  %local_2 = alloca i32, align 4
  store i64 %0, ptr %local_0, align 4
  %load_store_tmp = load i64, ptr %local_0, align 4
  store i64 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i64, ptr %local_1, align 4
  %trunc_dst = trunc i64 %cast_src to i32
  store i32 %trunc_dst, ptr %local_2, align 4
  %retval = load i32, ptr %local_2, align 4
  ret i32 %retval
}

define i64 @Test__cast_u64_as_u64(i64 %0) {
entry:
  %local_0 = alloca i64, align 8
  %local_1 = alloca i64, align 8
  %local_2 = alloca i64, align 8
  store i64 %0, ptr %local_0, align 4
  %load_store_tmp = load i64, ptr %local_0, align 4
  store i64 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i64, ptr %local_1, align 4
  store i64 %cast_src, ptr %local_2, align 4
  %retval = load i64, ptr %local_2, align 4
  ret i64 %retval
}

define i8 @Test__cast_u64_as_u8(i64 %0) {
entry:
  %local_0 = alloca i64, align 8
  %local_1 = alloca i64, align 8
  %local_2 = alloca i8, align 1
  store i64 %0, ptr %local_0, align 4
  %load_store_tmp = load i64, ptr %local_0, align 4
  store i64 %load_store_tmp, ptr %local_1, align 4
  %cast_src = load i64, ptr %local_1, align 4
  %trunc_dst = trunc i64 %cast_src to i8
  store i8 %trunc_dst, ptr %local_2, align 1
  %retval = load i8, ptr %local_2, align 1
  ret i8 %retval
}

define i128 @Test__cast_u8_as_u128(i8 %0) {
entry:
  %local_0 = alloca i8, align 1
  %local_1 = alloca i8, align 1
  %local_2 = alloca i128, align 8
  store i8 %0, ptr %local_0, align 1
  %load_store_tmp = load i8, ptr %local_0, align 1
  store i8 %load_store_tmp, ptr %local_1, align 1
  %cast_src = load i8, ptr %local_1, align 1
  %zext_dst = zext i8 %cast_src to i128
  store i128 %zext_dst, ptr %local_2, align 4
  %retval = load i128, ptr %local_2, align 4
  ret i128 %retval
}

define i16 @Test__cast_u8_as_u16(i8 %0) {
entry:
  %local_0 = alloca i8, align 1
  %local_1 = alloca i8, align 1
  %local_2 = alloca i16, align 2
  store i8 %0, ptr %local_0, align 1
  %load_store_tmp = load i8, ptr %local_0, align 1
  store i8 %load_store_tmp, ptr %local_1, align 1
  %cast_src = load i8, ptr %local_1, align 1
  %zext_dst = zext i8 %cast_src to i16
  store i16 %zext_dst, ptr %local_2, align 2
  %retval = load i16, ptr %local_2, align 2
  ret i16 %retval
}

define i256 @Test__cast_u8_as_u256(i8 %0) {
entry:
  %local_0 = alloca i8, align 1
  %local_1 = alloca i8, align 1
  %local_2 = alloca i256, align 8
  store i8 %0, ptr %local_0, align 1
  %load_store_tmp = load i8, ptr %local_0, align 1
  store i8 %load_store_tmp, ptr %local_1, align 1
  %cast_src = load i8, ptr %local_1, align 1
  %zext_dst = zext i8 %cast_src to i256
  store i256 %zext_dst, ptr %local_2, align 4
  %retval = load i256, ptr %local_2, align 4
  ret i256 %retval
}

define i32 @Test__cast_u8_as_u32(i8 %0) {
entry:
  %local_0 = alloca i8, align 1
  %local_1 = alloca i8, align 1
  %local_2 = alloca i32, align 4
  store i8 %0, ptr %local_0, align 1
  %load_store_tmp = load i8, ptr %local_0, align 1
  store i8 %load_store_tmp, ptr %local_1, align 1
  %cast_src = load i8, ptr %local_1, align 1
  %zext_dst = zext i8 %cast_src to i32
  store i32 %zext_dst, ptr %local_2, align 4
  %retval = load i32, ptr %local_2, align 4
  ret i32 %retval
}

define i64 @Test__cast_u8_as_u64(i8 %0) {
entry:
  %local_0 = alloca i8, align 1
  %local_1 = alloca i8, align 1
  %local_2 = alloca i64, align 8
  store i8 %0, ptr %local_0, align 1
  %load_store_tmp = load i8, ptr %local_0, align 1
  store i8 %load_store_tmp, ptr %local_1, align 1
  %cast_src = load i8, ptr %local_1, align 1
  %zext_dst = zext i8 %cast_src to i64
  store i64 %zext_dst, ptr %local_2, align 4
  %retval = load i64, ptr %local_2, align 4
  ret i64 %retval
}

define i8 @Test__cast_u8_as_u8(i8 %0) {
entry:
  %local_0 = alloca i8, align 1
  %local_1 = alloca i8, align 1
  %local_2 = alloca i8, align 1
  store i8 %0, ptr %local_0, align 1
  %load_store_tmp = load i8, ptr %local_0, align 1
  store i8 %load_store_tmp, ptr %local_1, align 1
  %cast_src = load i8, ptr %local_1, align 1
  store i8 %cast_src, ptr %local_2, align 1
  %retval = load i8, ptr %local_2, align 1
  ret i8 %retval
}
