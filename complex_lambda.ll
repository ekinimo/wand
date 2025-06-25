; ModuleID = 'wand_module'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%closure = type { i8*, i8* }  ; { function_ptr, env_ptr }
%env = type { i32, [0 x i32] }  ; { count, captured_values[] }

define i32 @add_intrinsic(i32 %a, i32 %b) {
entry:
  %result = add i32 %a, %b
  ret i32 %result
}

define i32 @call_closure_int(%closure* %closure_ptr, i32 %arg) {
entry:
  %func_ptr_ptr = getelementptr %closure, %closure* %closure_ptr, i32 0, i32 0
  %func_ptr_raw = load i8*, i8** %func_ptr_ptr
  %env_ptr_ptr = getelementptr %closure, %closure* %closure_ptr, i32 0, i32 1
  %env_ptr_raw = load i8*, i8** %env_ptr_ptr
  %func_ptr = bitcast i8* %func_ptr_raw to i32(i8*, i32)*
  %result = call i32 %func_ptr(i8* %env_ptr_raw, i32 %arg)
  ret i32 %result
}

define %closure* @call_closure_closure(%closure* %closure_ptr, i32 %arg) {
entry:
  %func_ptr_ptr = getelementptr %closure, %closure* %closure_ptr, i32 0, i32 0
  %func_ptr_raw = load i8*, i8** %func_ptr_ptr
  %env_ptr_ptr = getelementptr %closure, %closure* %closure_ptr, i32 0, i32 1
  %env_ptr_raw = load i8*, i8** %env_ptr_ptr
  %func_ptr = bitcast i8* %func_ptr_raw to %closure*(i8*, i32)*
  %result = call %closure* %func_ptr(i8* %env_ptr_raw, i32 %arg)
  ret %closure* %result
}

declare i32 @printf(i8*, ...)

@.str_int = private unnamed_addr constant [22 x i8] c"Type: Int, Value: %d\0A\00", align 1
@.str_closure = private unnamed_addr constant [34 x i8] c"Type: Function, Value: <closure>\0A\00", align 1
@.str_constructor = private unnamed_addr constant [30 x i8] c"Type: Constructor, Value: %s\0A\00", align 1
@.str_true = private unnamed_addr constant [5 x i8] c"True\00", align 1
@.str_false = private unnamed_addr constant [6 x i8] c"False\00", align 1
@.str_nothing = private unnamed_addr constant [8 x i8] c"Nothing\00", align 1
@.str_just = private unnamed_addr constant [8 x i8] c"Just %d\00", align 1

define void @print_constructor(i32 %ctor_val) {
entry:
  %tag = lshr i32 %ctor_val, 16
  %value = and i32 %ctor_val, 65535
  switch i32 %tag, label %default [
    i32 0, label %tag0
    i32 1, label %tag1
    i32 2, label %tag2
    i32 3, label %tag3
  ]

tag0:
  call i32 @printf(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str_constructor, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str_true, i32 0, i32 0))
  ret void

tag1:
  call i32 @printf(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str_constructor, i32 0, i32 0), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str_false, i32 0, i32 0))
  ret void

tag2:
  call i32 @printf(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str_constructor, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str_nothing, i32 0, i32 0))
  ret void

tag3:
  call i32 @printf(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str_just, i32 0, i32 0), i32 %value)
  ret void

default:
  call i32 @printf(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str_constructor, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str_nothing, i32 0, i32 0))
  ret void
}

declare i8* @malloc(i64)
declare void @free(i8*)

define i32 @main() {
entry:
  %18 = call i8* @malloc(i64 16)  ; sizeof(closure)
  %19 = bitcast i8* %18 to %closure*
  %20 = bitcast %closure*(i8*, i32)* @lambda_0 to i8*
  %21 = getelementptr %closure, %closure* %19, i32 0, i32 0
  store i8* %20, i8** %21
  %22 = getelementptr %closure, %closure* %19, i32 0, i32 1
  store i8* null, i8** %22
  %twice_addr = alloca %closure*
  store %closure* %19, %closure** %twice_addr
  %25 = call i8* @malloc(i64 16)  ; sizeof(closure)
  %26 = bitcast i8* %25 to %closure*
  %27 = bitcast i32(i8*, i32)* @lambda_1 to i8*
  %28 = getelementptr %closure, %closure* %26, i32 0, i32 0
  store i8* %27, i8** %28
  %29 = getelementptr %closure, %closure* %26, i32 0, i32 1
  store i8* null, i8** %29
  %increment_addr = alloca %closure*
  store %closure* %26, %closure** %increment_addr
  %30 = load %closure*, %closure** %twice_addr
  %31 = load %closure*, %closure** %increment_addr
  %33 = ptrtoint %closure* %31 to i64
  %34 = trunc i64 %33 to i32
  %32 = call i32 @call_closure_int(%closure* %30, i32 %34)
  %35 = call i32 @call_closure_int(%closure* %32, i32 5)
  call i32 @printf(i8* getelementptr inbounds ([22 x i8], [22 x i8]* @.str_int, i32 0, i32 0), i32 %35)
  ret i32 0
}

define %closure* @lambda_0(i8* %env, i32 %f) {
entry:
  %f_addr = alloca i32
  store i32 %f, i32* %f_addr
  %8 = call i8* @malloc(i64 16)  ; sizeof(closure)
  %9 = bitcast i8* %8 to %closure*
  %10 = bitcast i32(i8*, i32)* @lambda_0 to i8*
  %11 = getelementptr %closure, %closure* %9, i32 0, i32 0
  store i8* %10, i8** %11
  %12 = call i8* @malloc(i64 8)  ; sizeof(env)
  %13 = bitcast i8* %12 to %env*
  %14 = getelementptr %env, %env* %13, i32 0, i32 0
  store i32 1, i32* %14
  %15 = getelementptr %env, %env* %13, i32 0, i32 1, i32 0
  %16 = load i32, i32* %f_addr
  store i32 %16, i32* %15
  %17 = getelementptr %closure, %closure* %9, i32 0, i32 1
  store i8* %12, i8** %17
  ret %closure* %9
}

define i32 @lambda_1(i8* %env, i32 %y) {
entry:
  %y_addr = alloca i32
  store i32 %y, i32* %y_addr
  %23 = load i32, i32* %y_addr
  %24 = call i32 @add_intrinsic(i32 %23, i32 1)
  ret i32 %24
}


