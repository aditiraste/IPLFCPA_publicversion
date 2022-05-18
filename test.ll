; ModuleID = 'test.ll'
source_filename = "call_test4.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@y = dso_local global i32* null, align 8
@x = dso_local global i32* null, align 8
@z = dso_local global i32* null, align 8
@u = dso_local global i32 0, align 4

; Function Attrs: noinline nounwind uwtable
define dso_local i32* @fun(i32* %a) #0 {
entry:
  store i32* %a, i32** @y, align 8
  %i1 = load i32*, i32** @y, align 8
  ret i32* %i1
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 {
entry:
  %c = alloca i32, align 4
  store i32* %c, i32** @x, align 8
  %i = load i32*, i32** @x, align 8
  br label %0

0:                                                ; preds = %entry
  %call = call i32* @fun(i32* %i)
  br label %1

1:                                                ; preds = %0
  store i32* %call, i32** @z, align 8
  %i1 = load i32*, i32** @z, align 8
  %i2 = load i32, i32* %i1, align 4
  ret i32 %i2
}

attributes #0 = { noinline nounwind uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"Ubuntu clang version 12.0.1-++20211029101322+fed41342a82f-1~exp1~20211029221816.4"}
