//! Access to LLVM features not provided by the C API.
//!
//! Most or all copied from Rust.

#![allow(non_snake_case)]

use libc::{c_uint, size_t};
use llvm_sys::prelude::*;

pub fn AddFunctionAttributes<'ll>(
    llfn: LLVMValueRef,
    idx: AttributePlace,
    attrs: &[LLVMAttributeRef],
) {
    unsafe {
        LLVMRustAddFunctionAttributes(llfn, idx.as_uint(), attrs.as_ptr(), attrs.len());
    }
}

pub fn AddCallSiteAttributes<'ll>(
    llfn: LLVMValueRef,
    idx: AttributePlace,
    attrs: &[LLVMAttributeRef],
) {
    unsafe {
        LLVMRustAddCallSiteAttributes(llfn, idx.as_uint(), attrs.as_ptr(), attrs.len());
    }
}

#[derive(Copy, Clone)]
pub enum AttributePlace {
    ReturnValue,
    Argument(u32),
    Function,
}

impl AttributePlace {
    pub fn as_uint(self) -> c_uint {
        match self {
            AttributePlace::ReturnValue => 0,
            AttributePlace::Argument(i) => 1 + i,
            AttributePlace::Function => !0,
        }
    }
}

extern "C" {
    pub fn LLVMRustCreateAttrNoValue(C: LLVMContextRef, attr: AttributeKind) -> LLVMAttributeRef;

    fn LLVMRustAddFunctionAttributes(
        Fn: LLVMValueRef,
        index: c_uint,
        Attrs: *const LLVMAttributeRef,
        AttrsLen: size_t,
    );

    fn LLVMRustAddCallSiteAttributes(
        Instr: LLVMValueRef,
        index: c_uint,
        Attrs: *const LLVMAttributeRef,
        AttrsLen: size_t,
    );
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub enum AttributeKind {
    AlwaysInline = 0,
    ByVal = 1,
    Cold = 2,
    InlineHint = 3,
    MinSize = 4,
    Naked = 5,
    NoAlias = 6,
    NoCapture = 7,
    NoInline = 8,
    NonNull = 9,
    NoRedZone = 10,
    NoReturn = 11,
    NoUnwind = 12,
    OptimizeForSize = 13,
    ReadOnly = 14,
    SExt = 15,
    StructRet = 16,
    UWTable = 17,
    ZExt = 18,
    InReg = 19,
    SanitizeThread = 20,
    SanitizeAddress = 21,
    SanitizeMemory = 22,
    NonLazyBind = 23,
    OptimizeNone = 24,
    ReturnsTwice = 25,
    ReadNone = 26,
    InaccessibleMemOnly = 27,
    SanitizeHWAddress = 28,
    WillReturn = 29,
    StackProtectReq = 30,
    StackProtectStrong = 31,
    StackProtect = 32,
    NoUndef = 33,
    SanitizeMemTag = 34,
}
