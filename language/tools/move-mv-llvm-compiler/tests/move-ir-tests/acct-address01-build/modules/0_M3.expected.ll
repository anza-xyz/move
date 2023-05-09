; ModuleID = '0x100__M3'
source_filename = "<unknown>"

define i1 @M3__eq_address([32 x i8] %0, [32 x i8] %1) {
entry:
  %local_0 = alloca [32 x i8], align 1
  %local_1 = alloca [32 x i8], align 1
  %local_2 = alloca [32 x i8], align 1
  %local_3 = alloca [32 x i8], align 1
  %local_4 = alloca i1, align 1
  store [32 x i8] %0, ptr %local_0, align 1
  store [32 x i8] %1, ptr %local_1, align 1
  %eq_op0 = load <32 x i8>, ptr %local_0, align 32
  %eq_op1 = load <32 x i8>, ptr %local_1, align 32
  %addrcmp_dst = icmp eq <32 x i8> %eq_op0, %eq_op1
  %v2i = bitcast <32 x i1> %addrcmp_dst to i32
  %eq_dst = icmp ne i32 %v2i, 0
  store i1 %eq_dst, ptr %local_4, align 1
  %retval = load i1, ptr %local_4, align 1
  ret i1 %retval
}

define i1 @M3__ne_address([32 x i8] %0, [32 x i8] %1) {
entry:
  %local_0 = alloca [32 x i8], align 1
  %local_1 = alloca [32 x i8], align 1
  %local_2 = alloca [32 x i8], align 1
  %local_3 = alloca [32 x i8], align 1
  %local_4 = alloca i1, align 1
  store [32 x i8] %0, ptr %local_0, align 1
  store [32 x i8] %1, ptr %local_1, align 1
  %ne_op0 = load <32 x i8>, ptr %local_0, align 32
  %ne_op1 = load <32 x i8>, ptr %local_1, align 32
  %addrcmp_dst = icmp ne <32 x i8> %ne_op0, %ne_op1
  %v2i = bitcast <32 x i1> %addrcmp_dst to i32
  %ne_dst = icmp ne i32 %v2i, 0
  store i1 %ne_dst, ptr %local_4, align 1
  %retval = load i1, ptr %local_4, align 1
  ret i1 %retval
}

define ptr @M3__ret_address_ref(ptr %0) {
entry:
  %local_0 = alloca ptr, align 8
  %local_1 = alloca ptr, align 8
  store ptr %0, ptr %local_0, align 8
  %load_store_tmp = load ptr, ptr %local_0, align 8
  store ptr %load_store_tmp, ptr %local_1, align 8
  %retval = load ptr, ptr %local_1, align 8
  ret ptr %retval
}

define [32 x i8] @M3__use_address_ref(ptr %0) {
entry:
  %local_0 = alloca ptr, align 8
  %local_1 = alloca ptr, align 8
  %local_2 = alloca [32 x i8], align 1
  store ptr %0, ptr %local_0, align 8
  %load_store_tmp = load ptr, ptr %local_0, align 8
  store ptr %load_store_tmp, ptr %local_1, align 8
  %load_deref_store_tmp1 = load ptr, ptr %local_1, align 8
  %load_deref_store_tmp2 = load [32 x i8], ptr %load_deref_store_tmp1, align 1
  store [32 x i8] %load_deref_store_tmp2, ptr %local_2, align 1
  %retval = load [32 x i8], ptr %local_2, align 1
  ret [32 x i8] %retval
}

define [32 x i8] @M3__use_address_val([32 x i8] %0) {
entry:
  %local_0 = alloca [32 x i8], align 1
  %local_1 = alloca [32 x i8], align 1
  store [32 x i8] %0, ptr %local_0, align 1
  %retval = load [32 x i8], ptr %local_0, align 1
  ret [32 x i8] %retval
}
