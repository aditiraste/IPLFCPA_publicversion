; ModuleID = 'lbm.ll'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque
%struct.MAIN_Param = type { i32, i8*, i32, i32, i8* }
%struct.stat = type { i64, i64, i64, i32, i32, i32, i32, i64, i64, i64, i64, %struct.timespec, %struct.timespec, %struct.timespec, [3 x i64] }
%struct.timespec = type { i64, i64 }

@.str = private unnamed_addr constant [49 x i8] c"LBM_allocateGrid: could not allocate %.1f MByte\0A\00", align 1
@.str.1 = private unnamed_addr constant [3 x i8] c"rb\00", align 1
@.str.2 = private unnamed_addr constant [138 x i8] c"LBM_showGridStatistics:\0A\09nObstacleCells: %7i nAccelCells: %7i nFluidCells: %7i\0A\09minRho: %8.4f maxRho: %8.4f mass: %e\0A\09minU: %e maxU: %e\0A\0A\00", align 1
@.str.3 = private unnamed_addr constant [3 x i8] c"wb\00", align 1
@.str.4 = private unnamed_addr constant [2 x i8] c"w\00", align 1
@.str.5 = private unnamed_addr constant [10 x i8] c"%e %e %e\0A\00", align 1
@.str.6 = private unnamed_addr constant [2 x i8] c"r\00", align 1
@.str.7 = private unnamed_addr constant [10 x i8] c"%f %f %f\0A\00", align 1
@.str.8 = private unnamed_addr constant [43 x i8] c"LBM_compareVelocityField: maxDiff = %e  \0A\0A\00", align 1
@srcGrid = internal global [26000000 x double]* null, align 8
@dstGrid = internal global [26000000 x double]* null, align 8
@.str.9 = private unnamed_addr constant [14 x i8] c"timestep: %i\0A\00", align 1
@__const.MAIN_printInfo.actionString = private unnamed_addr constant [3 x [32 x i8]] [[32 x i8] c"nothing\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", [32 x i8] c"compare\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", [32 x i8] c"store\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"], align 16
@__const.MAIN_printInfo.simTypeString = private unnamed_addr constant [3 x [32 x i8]] [[32 x i8] c"lid-driven cavity\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", [32 x i8] c"channel flow\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", [32 x i8] zeroinitializer], align 16
@.str.6.10 = private unnamed_addr constant [7 x i8] c"<none>\00", align 1
@.str.5.11 = private unnamed_addr constant [174 x i8] c"MAIN_printInfo:\0A\09grid size      : %i x %i x %i = %.2f * 10^6 Cells\0A\09nTimeSteps     : %i\0A\09result file    : %s\0A\09action         : %s\0A\09simulation type: %s\0A\09obstacle file  : %s\0A\0A\00", align 1
@.str.1.12 = private unnamed_addr constant [109 x i8] c"syntax: lbm <time steps> <result file> <0: nil, 1: cmp, 2: str> <0: ldc, 1: channel flow> [<obstacle file>]\0A\00", align 1
@.str.2.13 = private unnamed_addr constant [55 x i8] c"MAIN_parseCommandLine: cannot stat obstacle file '%s'\0A\00", align 1
@.str.3.14 = private unnamed_addr constant [82 x i8] c"MAIN_parseCommandLine:\0A\09size of file '%s' is %i bytes\0A\09expected size is %i bytes\0A\00", align 1
@.str.4.15 = private unnamed_addr constant [53 x i8] c"MAIN_parseCommandLine: cannot stat result file '%s'\0A\00", align 1

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_allocateGrid(double** %ptr) #0 {
entry:
  %call = call noalias i8* @malloc(i64 214400000) #6
  %i = bitcast i8* %call to double*
  store double* %i, double** %ptr, align 8
  %i1 = load double*, double** %ptr, align 8
  %tobool = icmp ne double* %i1, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %call1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str, i64 0, i64 0), double 0x40698EF800000000)
  call void @exit(i32 1) #7
  unreachable

if.end:                                           ; preds = %entry
  %i2 = load double*, double** %ptr, align 8
  %add.ptr = getelementptr inbounds double, double* %i2, i64 400000
  store double* %add.ptr, double** %ptr, align 8
  ret void
}

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i64) #1

declare dso_local i32 @printf(i8*, ...) #2

; Function Attrs: noreturn nounwind
declare dso_local void @exit(i32) #3

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_freeGrid(double** %ptr) #0 {
entry:
  %i = load double*, double** %ptr, align 8
  %add.ptr = getelementptr inbounds double, double* %i, i64 -400000
  %i1 = bitcast double* %add.ptr to i8*
  call void @free(i8* %i1) #6
  store double* null, double** %ptr, align 8
  ret void
}

; Function Attrs: nounwind
declare dso_local void @free(i8*) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_initializeGrid(double* %grid) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ -400000, %entry ], [ %add58, %for.inc ]
  %cmp = icmp slt i32 %i.0, 26400000
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %add = add nsw i32 0, %i.0
  %idxprom = sext i32 %add to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  store double 0x3FD5555555555555, double* %arrayidx, align 8
  %add1 = add nsw i32 1, %i.0
  %idxprom2 = sext i32 %add1 to i64
  %arrayidx3 = getelementptr inbounds double, double* %grid, i64 %idxprom2
  store double 0x3FAC71C71C71C71C, double* %arrayidx3, align 8
  %add4 = add nsw i32 2, %i.0
  %idxprom5 = sext i32 %add4 to i64
  %arrayidx6 = getelementptr inbounds double, double* %grid, i64 %idxprom5
  store double 0x3FAC71C71C71C71C, double* %arrayidx6, align 8
  %add7 = add nsw i32 3, %i.0
  %idxprom8 = sext i32 %add7 to i64
  %arrayidx9 = getelementptr inbounds double, double* %grid, i64 %idxprom8
  store double 0x3FAC71C71C71C71C, double* %arrayidx9, align 8
  %add10 = add nsw i32 4, %i.0
  %idxprom11 = sext i32 %add10 to i64
  %arrayidx12 = getelementptr inbounds double, double* %grid, i64 %idxprom11
  store double 0x3FAC71C71C71C71C, double* %arrayidx12, align 8
  %add13 = add nsw i32 5, %i.0
  %idxprom14 = sext i32 %add13 to i64
  %arrayidx15 = getelementptr inbounds double, double* %grid, i64 %idxprom14
  store double 0x3FAC71C71C71C71C, double* %arrayidx15, align 8
  %add16 = add nsw i32 6, %i.0
  %idxprom17 = sext i32 %add16 to i64
  %arrayidx18 = getelementptr inbounds double, double* %grid, i64 %idxprom17
  store double 0x3FAC71C71C71C71C, double* %arrayidx18, align 8
  %add19 = add nsw i32 7, %i.0
  %idxprom20 = sext i32 %add19 to i64
  %arrayidx21 = getelementptr inbounds double, double* %grid, i64 %idxprom20
  store double 0x3F9C71C71C71C71C, double* %arrayidx21, align 8
  %add22 = add nsw i32 8, %i.0
  %idxprom23 = sext i32 %add22 to i64
  %arrayidx24 = getelementptr inbounds double, double* %grid, i64 %idxprom23
  store double 0x3F9C71C71C71C71C, double* %arrayidx24, align 8
  %add25 = add nsw i32 9, %i.0
  %idxprom26 = sext i32 %add25 to i64
  %arrayidx27 = getelementptr inbounds double, double* %grid, i64 %idxprom26
  store double 0x3F9C71C71C71C71C, double* %arrayidx27, align 8
  %add28 = add nsw i32 10, %i.0
  %idxprom29 = sext i32 %add28 to i64
  %arrayidx30 = getelementptr inbounds double, double* %grid, i64 %idxprom29
  store double 0x3F9C71C71C71C71C, double* %arrayidx30, align 8
  %add31 = add nsw i32 11, %i.0
  %idxprom32 = sext i32 %add31 to i64
  %arrayidx33 = getelementptr inbounds double, double* %grid, i64 %idxprom32
  store double 0x3F9C71C71C71C71C, double* %arrayidx33, align 8
  %add34 = add nsw i32 12, %i.0
  %idxprom35 = sext i32 %add34 to i64
  %arrayidx36 = getelementptr inbounds double, double* %grid, i64 %idxprom35
  store double 0x3F9C71C71C71C71C, double* %arrayidx36, align 8
  %add37 = add nsw i32 13, %i.0
  %idxprom38 = sext i32 %add37 to i64
  %arrayidx39 = getelementptr inbounds double, double* %grid, i64 %idxprom38
  store double 0x3F9C71C71C71C71C, double* %arrayidx39, align 8
  %add40 = add nsw i32 14, %i.0
  %idxprom41 = sext i32 %add40 to i64
  %arrayidx42 = getelementptr inbounds double, double* %grid, i64 %idxprom41
  store double 0x3F9C71C71C71C71C, double* %arrayidx42, align 8
  %add43 = add nsw i32 15, %i.0
  %idxprom44 = sext i32 %add43 to i64
  %arrayidx45 = getelementptr inbounds double, double* %grid, i64 %idxprom44
  store double 0x3F9C71C71C71C71C, double* %arrayidx45, align 8
  %add46 = add nsw i32 16, %i.0
  %idxprom47 = sext i32 %add46 to i64
  %arrayidx48 = getelementptr inbounds double, double* %grid, i64 %idxprom47
  store double 0x3F9C71C71C71C71C, double* %arrayidx48, align 8
  %add49 = add nsw i32 17, %i.0
  %idxprom50 = sext i32 %add49 to i64
  %arrayidx51 = getelementptr inbounds double, double* %grid, i64 %idxprom50
  store double 0x3F9C71C71C71C71C, double* %arrayidx51, align 8
  %add52 = add nsw i32 18, %i.0
  %idxprom53 = sext i32 %add52 to i64
  %arrayidx54 = getelementptr inbounds double, double* %grid, i64 %idxprom53
  store double 0x3F9C71C71C71C71C, double* %arrayidx54, align 8
  %add55 = add nsw i32 19, %i.0
  %idxprom56 = sext i32 %add55 to i64
  %arrayidx57 = getelementptr inbounds double, double* %grid, i64 %idxprom56
  %i = bitcast double* %arrayidx57 to i8*
  %i1 = bitcast i8* %i to i32*
  store i32 0, i32* %i1, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %add58 = add nsw i32 %i.0, 20
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_swapGrids([26000000 x double]** %grid1, [26000000 x double]** %grid2) #0 {
entry:
  %i = load [26000000 x double]*, [26000000 x double]** %grid1, align 8
  %i1 = load [26000000 x double]*, [26000000 x double]** %grid2, align 8
  store [26000000 x double]* %i1, [26000000 x double]** %grid1, align 8
  store [26000000 x double]* %i, [26000000 x double]** %grid2, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_loadObstacleFile(double* %grid, i8* %filename) #0 {
entry:
  %call = call noalias %struct._IO_FILE* @fopen(i8* %filename, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1, i64 0, i64 0))
  br label %for.cond

for.cond:                                         ; preds = %for.inc19, %entry
  %z.0 = phi i32 [ 0, %entry ], [ %inc20, %for.inc19 ]
  %cmp = icmp slt i32 %z.0, 130
  br i1 %cmp, label %for.body, label %for.end21

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc15, %for.body
  %y.0 = phi i32 [ 0, %for.body ], [ %inc16, %for.inc15 ]
  %cmp2 = icmp slt i32 %y.0, 100
  br i1 %cmp2, label %for.body3, label %for.end17

for.body3:                                        ; preds = %for.cond1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body3
  %x.0 = phi i32 [ 0, %for.body3 ], [ %inc, %for.inc ]
  %cmp5 = icmp slt i32 %x.0, 100
  br i1 %cmp5, label %for.body6, label %for.end

for.body6:                                        ; preds = %for.cond4
  %call7 = call i32 @fgetc(%struct._IO_FILE* %call)
  %cmp8 = icmp ne i32 %call7, 46
  br i1 %cmp8, label %if.then, label %if.end

if.then:                                          ; preds = %for.body6
  %mul = mul nsw i32 %y.0, 100
  %add = add nsw i32 %x.0, %mul
  %mul9 = mul nsw i32 %z.0, 100
  %mul10 = mul nsw i32 %mul9, 100
  %add11 = add nsw i32 %add, %mul10
  %mul12 = mul nsw i32 20, %add11
  %add13 = add nsw i32 19, %mul12
  %idxprom = sext i32 %add13 to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  %i = bitcast double* %arrayidx to i8*
  %i1 = bitcast i8* %i to i32*
  %i2 = load i32, i32* %i1, align 4
  %or = or i32 %i2, 1
  store i32 %or, i32* %i1, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body6
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %inc = add nsw i32 %x.0, 1
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  %call14 = call i32 @fgetc(%struct._IO_FILE* %call)
  br label %for.inc15

for.inc15:                                        ; preds = %for.end
  %inc16 = add nsw i32 %y.0, 1
  br label %for.cond1

for.end17:                                        ; preds = %for.cond1
  %call18 = call i32 @fgetc(%struct._IO_FILE* %call)
  br label %for.inc19

for.inc19:                                        ; preds = %for.end17
  %inc20 = add nsw i32 %z.0, 1
  br label %for.cond

for.end21:                                        ; preds = %for.cond
  %call22 = call i32 @fclose(%struct._IO_FILE* %call)
  ret void
}

declare dso_local noalias %struct._IO_FILE* @fopen(i8*, i8*) #2

declare dso_local i32 @fgetc(%struct._IO_FILE*) #2

declare dso_local i32 @fclose(%struct._IO_FILE*) #2

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_initializeSpecialCellsForLDC(double* %grid) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc48, %entry
  %z.0 = phi i32 [ -2, %entry ], [ %inc49, %for.inc48 ]
  %cmp = icmp slt i32 %z.0, 132
  br i1 %cmp, label %for.body, label %for.end50

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc45, %for.body
  %y.0 = phi i32 [ 0, %for.body ], [ %inc46, %for.inc45 ]
  %cmp2 = icmp slt i32 %y.0, 100
  br i1 %cmp2, label %for.body3, label %for.end47

for.body3:                                        ; preds = %for.cond1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body3
  %x.0 = phi i32 [ 0, %for.body3 ], [ %inc, %for.inc ]
  %cmp5 = icmp slt i32 %x.0, 100
  br i1 %cmp5, label %for.body6, label %for.end

for.body6:                                        ; preds = %for.cond4
  %cmp7 = icmp eq i32 %x.0, 0
  br i1 %cmp7, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %for.body6
  %cmp8 = icmp eq i32 %x.0, 99
  br i1 %cmp8, label %if.then, label %lor.lhs.false9

lor.lhs.false9:                                   ; preds = %lor.lhs.false
  %cmp10 = icmp eq i32 %y.0, 0
  br i1 %cmp10, label %if.then, label %lor.lhs.false11

lor.lhs.false11:                                  ; preds = %lor.lhs.false9
  %cmp12 = icmp eq i32 %y.0, 99
  br i1 %cmp12, label %if.then, label %lor.lhs.false13

lor.lhs.false13:                                  ; preds = %lor.lhs.false11
  %cmp14 = icmp eq i32 %z.0, 0
  br i1 %cmp14, label %if.then, label %lor.lhs.false15

lor.lhs.false15:                                  ; preds = %lor.lhs.false13
  %cmp16 = icmp eq i32 %z.0, 129
  br i1 %cmp16, label %if.then, label %if.else

if.then:                                          ; preds = %lor.lhs.false15, %lor.lhs.false13, %lor.lhs.false11, %lor.lhs.false9, %lor.lhs.false, %for.body6
  %mul = mul nsw i32 %y.0, 100
  %add = add nsw i32 %x.0, %mul
  %mul17 = mul nsw i32 %z.0, 100
  %mul18 = mul nsw i32 %mul17, 100
  %add19 = add nsw i32 %add, %mul18
  %mul20 = mul nsw i32 20, %add19
  %add21 = add nsw i32 19, %mul20
  %idxprom = sext i32 %add21 to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  %i = bitcast double* %arrayidx to i8*
  %i1 = bitcast i8* %i to i32*
  %i2 = load i32, i32* %i1, align 4
  %or = or i32 %i2, 1
  store i32 %or, i32* %i1, align 4
  br label %if.end44

if.else:                                          ; preds = %lor.lhs.false15
  %cmp22 = icmp eq i32 %z.0, 1
  br i1 %cmp22, label %land.lhs.true, label %lor.lhs.false23

lor.lhs.false23:                                  ; preds = %if.else
  %cmp24 = icmp eq i32 %z.0, 128
  br i1 %cmp24, label %land.lhs.true, label %if.end

land.lhs.true:                                    ; preds = %lor.lhs.false23, %if.else
  %cmp25 = icmp sgt i32 %x.0, 1
  br i1 %cmp25, label %land.lhs.true26, label %if.end

land.lhs.true26:                                  ; preds = %land.lhs.true
  %cmp27 = icmp slt i32 %x.0, 98
  br i1 %cmp27, label %land.lhs.true28, label %if.end

land.lhs.true28:                                  ; preds = %land.lhs.true26
  %cmp29 = icmp sgt i32 %y.0, 1
  br i1 %cmp29, label %land.lhs.true30, label %if.end

land.lhs.true30:                                  ; preds = %land.lhs.true28
  %cmp31 = icmp slt i32 %y.0, 98
  br i1 %cmp31, label %if.then32, label %if.end

if.then32:                                        ; preds = %land.lhs.true30
  %mul34 = mul nsw i32 %y.0, 100
  %add35 = add nsw i32 %x.0, %mul34
  %mul36 = mul nsw i32 %z.0, 100
  %mul37 = mul nsw i32 %mul36, 100
  %add38 = add nsw i32 %add35, %mul37
  %mul39 = mul nsw i32 20, %add38
  %add40 = add nsw i32 19, %mul39
  %idxprom41 = sext i32 %add40 to i64
  %arrayidx42 = getelementptr inbounds double, double* %grid, i64 %idxprom41
  %i3 = bitcast double* %arrayidx42 to i8*
  %i4 = bitcast i8* %i3 to i32*
  %i5 = load i32, i32* %i4, align 4
  %or43 = or i32 %i5, 2
  store i32 %or43, i32* %i4, align 4
  br label %if.end

if.end:                                           ; preds = %if.then32, %land.lhs.true30, %land.lhs.true28, %land.lhs.true26, %land.lhs.true, %lor.lhs.false23
  br label %if.end44

if.end44:                                         ; preds = %if.end, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end44
  %inc = add nsw i32 %x.0, 1
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  br label %for.inc45

for.inc45:                                        ; preds = %for.end
  %inc46 = add nsw i32 %y.0, 1
  br label %for.cond1

for.end47:                                        ; preds = %for.cond1
  br label %for.inc48

for.inc48:                                        ; preds = %for.end47
  %inc49 = add nsw i32 %z.0, 1
  br label %for.cond

for.end50:                                        ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_initializeSpecialCellsForChannel(double* %grid) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc46, %entry
  %z.0 = phi i32 [ -2, %entry ], [ %inc47, %for.inc46 ]
  %cmp = icmp slt i32 %z.0, 132
  br i1 %cmp, label %for.body, label %for.end48

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc43, %for.body
  %y.0 = phi i32 [ 0, %for.body ], [ %inc44, %for.inc43 ]
  %cmp2 = icmp slt i32 %y.0, 100
  br i1 %cmp2, label %for.body3, label %for.end45

for.body3:                                        ; preds = %for.cond1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body3
  %x.0 = phi i32 [ 0, %for.body3 ], [ %inc, %for.inc ]
  %cmp5 = icmp slt i32 %x.0, 100
  br i1 %cmp5, label %for.body6, label %for.end

for.body6:                                        ; preds = %for.cond4
  %cmp7 = icmp eq i32 %x.0, 0
  br i1 %cmp7, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %for.body6
  %cmp8 = icmp eq i32 %x.0, 99
  br i1 %cmp8, label %if.then, label %lor.lhs.false9

lor.lhs.false9:                                   ; preds = %lor.lhs.false
  %cmp10 = icmp eq i32 %y.0, 0
  br i1 %cmp10, label %if.then, label %lor.lhs.false11

lor.lhs.false11:                                  ; preds = %lor.lhs.false9
  %cmp12 = icmp eq i32 %y.0, 99
  br i1 %cmp12, label %if.then, label %if.end42

if.then:                                          ; preds = %lor.lhs.false11, %lor.lhs.false9, %lor.lhs.false, %for.body6
  %mul = mul nsw i32 %y.0, 100
  %add = add nsw i32 %x.0, %mul
  %mul13 = mul nsw i32 %z.0, 100
  %mul14 = mul nsw i32 %mul13, 100
  %add15 = add nsw i32 %add, %mul14
  %mul16 = mul nsw i32 20, %add15
  %add17 = add nsw i32 19, %mul16
  %idxprom = sext i32 %add17 to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  %i = bitcast double* %arrayidx to i8*
  %i1 = bitcast i8* %i to i32*
  %i2 = load i32, i32* %i1, align 4
  %or = or i32 %i2, 1
  store i32 %or, i32* %i1, align 4
  %cmp18 = icmp eq i32 %z.0, 0
  br i1 %cmp18, label %land.lhs.true, label %lor.lhs.false19

lor.lhs.false19:                                  ; preds = %if.then
  %cmp20 = icmp eq i32 %z.0, 129
  br i1 %cmp20, label %land.lhs.true, label %if.end

land.lhs.true:                                    ; preds = %lor.lhs.false19, %if.then
  %mul21 = mul nsw i32 %y.0, 100
  %add22 = add nsw i32 %x.0, %mul21
  %mul23 = mul nsw i32 %z.0, 100
  %mul24 = mul nsw i32 %mul23, 100
  %add25 = add nsw i32 %add22, %mul24
  %mul26 = mul nsw i32 20, %add25
  %add27 = add nsw i32 19, %mul26
  %idxprom28 = sext i32 %add27 to i64
  %arrayidx29 = getelementptr inbounds double, double* %grid, i64 %idxprom28
  %i3 = bitcast double* %arrayidx29 to i8*
  %i4 = bitcast i8* %i3 to i32*
  %i5 = load i32, i32* %i4, align 4
  %and = and i32 %i5, 1
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.end, label %if.then30

if.then30:                                        ; preds = %land.lhs.true
  %mul32 = mul nsw i32 %y.0, 100
  %add33 = add nsw i32 %x.0, %mul32
  %mul34 = mul nsw i32 %z.0, 100
  %mul35 = mul nsw i32 %mul34, 100
  %add36 = add nsw i32 %add33, %mul35
  %mul37 = mul nsw i32 20, %add36
  %add38 = add nsw i32 19, %mul37
  %idxprom39 = sext i32 %add38 to i64
  %arrayidx40 = getelementptr inbounds double, double* %grid, i64 %idxprom39
  %i6 = bitcast double* %arrayidx40 to i8*
  %i7 = bitcast i8* %i6 to i32*
  %i8 = load i32, i32* %i7, align 4
  %or41 = or i32 %i8, 4
  store i32 %or41, i32* %i7, align 4
  br label %if.end

if.end:                                           ; preds = %if.then30, %land.lhs.true, %lor.lhs.false19
  br label %if.end42

if.end42:                                         ; preds = %if.end, %lor.lhs.false11
  br label %for.inc

for.inc:                                          ; preds = %if.end42
  %inc = add nsw i32 %x.0, 1
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  br label %for.inc43

for.inc43:                                        ; preds = %for.end
  %inc44 = add nsw i32 %y.0, 1
  br label %for.cond1

for.end45:                                        ; preds = %for.cond1
  br label %for.inc46

for.inc46:                                        ; preds = %for.end45
  %inc47 = add nsw i32 %z.0, 1
  br label %for.cond

for.end48:                                        ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_performStreamCollide(double* %srcGrid, double* %dstGrid) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %add636, %for.inc ]
  %cmp = icmp slt i32 %i.0, 26000000
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %add = add nsw i32 19, %i.0
  %idxprom = sext i32 %add to i64
  %arrayidx = getelementptr inbounds double, double* %srcGrid, i64 %idxprom
  %i = bitcast double* %arrayidx to i8*
  %i1 = bitcast i8* %i to i32*
  %i2 = load i32, i32* %i1, align 4
  %and = and i32 %i2, 1
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  %add1 = add nsw i32 0, %i.0
  %idxprom2 = sext i32 %add1 to i64
  %arrayidx3 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom2
  %i3 = load double, double* %arrayidx3, align 8
  %add4 = add nsw i32 0, %i.0
  %idxprom5 = sext i32 %add4 to i64
  %arrayidx6 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom5
  store double %i3, double* %arrayidx6, align 8
  %add7 = add nsw i32 1, %i.0
  %idxprom8 = sext i32 %add7 to i64
  %arrayidx9 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom8
  %i4 = load double, double* %arrayidx9, align 8
  %add10 = add nsw i32 -1998, %i.0
  %idxprom11 = sext i32 %add10 to i64
  %arrayidx12 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom11
  store double %i4, double* %arrayidx12, align 8
  %add13 = add nsw i32 2, %i.0
  %idxprom14 = sext i32 %add13 to i64
  %arrayidx15 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom14
  %i5 = load double, double* %arrayidx15, align 8
  %add16 = add nsw i32 2001, %i.0
  %idxprom17 = sext i32 %add16 to i64
  %arrayidx18 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom17
  store double %i5, double* %arrayidx18, align 8
  %add19 = add nsw i32 3, %i.0
  %idxprom20 = sext i32 %add19 to i64
  %arrayidx21 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom20
  %i6 = load double, double* %arrayidx21, align 8
  %add22 = add nsw i32 -16, %i.0
  %idxprom23 = sext i32 %add22 to i64
  %arrayidx24 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom23
  store double %i6, double* %arrayidx24, align 8
  %add25 = add nsw i32 4, %i.0
  %idxprom26 = sext i32 %add25 to i64
  %arrayidx27 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom26
  %i7 = load double, double* %arrayidx27, align 8
  %add28 = add nsw i32 23, %i.0
  %idxprom29 = sext i32 %add28 to i64
  %arrayidx30 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom29
  store double %i7, double* %arrayidx30, align 8
  %add31 = add nsw i32 5, %i.0
  %idxprom32 = sext i32 %add31 to i64
  %arrayidx33 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom32
  %i8 = load double, double* %arrayidx33, align 8
  %add34 = add nsw i32 -199994, %i.0
  %idxprom35 = sext i32 %add34 to i64
  %arrayidx36 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom35
  store double %i8, double* %arrayidx36, align 8
  %add37 = add nsw i32 6, %i.0
  %idxprom38 = sext i32 %add37 to i64
  %arrayidx39 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom38
  %i9 = load double, double* %arrayidx39, align 8
  %add40 = add nsw i32 200005, %i.0
  %idxprom41 = sext i32 %add40 to i64
  %arrayidx42 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom41
  store double %i9, double* %arrayidx42, align 8
  %add43 = add nsw i32 7, %i.0
  %idxprom44 = sext i32 %add43 to i64
  %arrayidx45 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom44
  %i10 = load double, double* %arrayidx45, align 8
  %add46 = add nsw i32 -2010, %i.0
  %idxprom47 = sext i32 %add46 to i64
  %arrayidx48 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom47
  store double %i10, double* %arrayidx48, align 8
  %add49 = add nsw i32 8, %i.0
  %idxprom50 = sext i32 %add49 to i64
  %arrayidx51 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom50
  %i11 = load double, double* %arrayidx51, align 8
  %add52 = add nsw i32 -1971, %i.0
  %idxprom53 = sext i32 %add52 to i64
  %arrayidx54 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom53
  store double %i11, double* %arrayidx54, align 8
  %add55 = add nsw i32 9, %i.0
  %idxprom56 = sext i32 %add55 to i64
  %arrayidx57 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom56
  %i12 = load double, double* %arrayidx57, align 8
  %add58 = add nsw i32 1988, %i.0
  %idxprom59 = sext i32 %add58 to i64
  %arrayidx60 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom59
  store double %i12, double* %arrayidx60, align 8
  %add61 = add nsw i32 10, %i.0
  %idxprom62 = sext i32 %add61 to i64
  %arrayidx63 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom62
  %i13 = load double, double* %arrayidx63, align 8
  %add64 = add nsw i32 2027, %i.0
  %idxprom65 = sext i32 %add64 to i64
  %arrayidx66 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom65
  store double %i13, double* %arrayidx66, align 8
  %add67 = add nsw i32 11, %i.0
  %idxprom68 = sext i32 %add67 to i64
  %arrayidx69 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom68
  %i14 = load double, double* %arrayidx69, align 8
  %add70 = add nsw i32 -201986, %i.0
  %idxprom71 = sext i32 %add70 to i64
  %arrayidx72 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom71
  store double %i14, double* %arrayidx72, align 8
  %add73 = add nsw i32 12, %i.0
  %idxprom74 = sext i32 %add73 to i64
  %arrayidx75 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom74
  %i15 = load double, double* %arrayidx75, align 8
  %add76 = add nsw i32 198013, %i.0
  %idxprom77 = sext i32 %add76 to i64
  %arrayidx78 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom77
  store double %i15, double* %arrayidx78, align 8
  %add79 = add nsw i32 13, %i.0
  %idxprom80 = sext i32 %add79 to i64
  %arrayidx81 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom80
  %i16 = load double, double* %arrayidx81, align 8
  %add82 = add nsw i32 -197988, %i.0
  %idxprom83 = sext i32 %add82 to i64
  %arrayidx84 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom83
  store double %i16, double* %arrayidx84, align 8
  %add85 = add nsw i32 14, %i.0
  %idxprom86 = sext i32 %add85 to i64
  %arrayidx87 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom86
  %i17 = load double, double* %arrayidx87, align 8
  %add88 = add nsw i32 202011, %i.0
  %idxprom89 = sext i32 %add88 to i64
  %arrayidx90 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom89
  store double %i17, double* %arrayidx90, align 8
  %add91 = add nsw i32 15, %i.0
  %idxprom92 = sext i32 %add91 to i64
  %arrayidx93 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom92
  %i18 = load double, double* %arrayidx93, align 8
  %add94 = add nsw i32 -200002, %i.0
  %idxprom95 = sext i32 %add94 to i64
  %arrayidx96 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom95
  store double %i18, double* %arrayidx96, align 8
  %add97 = add nsw i32 16, %i.0
  %idxprom98 = sext i32 %add97 to i64
  %arrayidx99 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom98
  %i19 = load double, double* %arrayidx99, align 8
  %add100 = add nsw i32 199997, %i.0
  %idxprom101 = sext i32 %add100 to i64
  %arrayidx102 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom101
  store double %i19, double* %arrayidx102, align 8
  %add103 = add nsw i32 17, %i.0
  %idxprom104 = sext i32 %add103 to i64
  %arrayidx105 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom104
  %i20 = load double, double* %arrayidx105, align 8
  %add106 = add nsw i32 -199964, %i.0
  %idxprom107 = sext i32 %add106 to i64
  %arrayidx108 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom107
  store double %i20, double* %arrayidx108, align 8
  %add109 = add nsw i32 18, %i.0
  %idxprom110 = sext i32 %add109 to i64
  %arrayidx111 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom110
  %i21 = load double, double* %arrayidx111, align 8
  %add112 = add nsw i32 200035, %i.0
  %idxprom113 = sext i32 %add112 to i64
  %arrayidx114 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom113
  store double %i21, double* %arrayidx114, align 8
  br label %for.inc

if.end:                                           ; preds = %for.body
  %add115 = add nsw i32 0, %i.0
  %idxprom116 = sext i32 %add115 to i64
  %arrayidx117 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom116
  %i22 = load double, double* %arrayidx117, align 8
  %add118 = add nsw i32 1, %i.0
  %idxprom119 = sext i32 %add118 to i64
  %arrayidx120 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom119
  %i23 = load double, double* %arrayidx120, align 8
  %add121 = fadd double %i22, %i23
  %add122 = add nsw i32 2, %i.0
  %idxprom123 = sext i32 %add122 to i64
  %arrayidx124 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom123
  %i24 = load double, double* %arrayidx124, align 8
  %add125 = fadd double %add121, %i24
  %add126 = add nsw i32 3, %i.0
  %idxprom127 = sext i32 %add126 to i64
  %arrayidx128 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom127
  %i25 = load double, double* %arrayidx128, align 8
  %add129 = fadd double %add125, %i25
  %add130 = add nsw i32 4, %i.0
  %idxprom131 = sext i32 %add130 to i64
  %arrayidx132 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom131
  %i26 = load double, double* %arrayidx132, align 8
  %add133 = fadd double %add129, %i26
  %add134 = add nsw i32 5, %i.0
  %idxprom135 = sext i32 %add134 to i64
  %arrayidx136 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom135
  %i27 = load double, double* %arrayidx136, align 8
  %add137 = fadd double %add133, %i27
  %add138 = add nsw i32 6, %i.0
  %idxprom139 = sext i32 %add138 to i64
  %arrayidx140 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom139
  %i28 = load double, double* %arrayidx140, align 8
  %add141 = fadd double %add137, %i28
  %add142 = add nsw i32 7, %i.0
  %idxprom143 = sext i32 %add142 to i64
  %arrayidx144 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom143
  %i29 = load double, double* %arrayidx144, align 8
  %add145 = fadd double %add141, %i29
  %add146 = add nsw i32 8, %i.0
  %idxprom147 = sext i32 %add146 to i64
  %arrayidx148 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom147
  %i30 = load double, double* %arrayidx148, align 8
  %add149 = fadd double %add145, %i30
  %add150 = add nsw i32 9, %i.0
  %idxprom151 = sext i32 %add150 to i64
  %arrayidx152 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom151
  %i31 = load double, double* %arrayidx152, align 8
  %add153 = fadd double %add149, %i31
  %add154 = add nsw i32 10, %i.0
  %idxprom155 = sext i32 %add154 to i64
  %arrayidx156 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom155
  %i32 = load double, double* %arrayidx156, align 8
  %add157 = fadd double %add153, %i32
  %add158 = add nsw i32 11, %i.0
  %idxprom159 = sext i32 %add158 to i64
  %arrayidx160 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom159
  %i33 = load double, double* %arrayidx160, align 8
  %add161 = fadd double %add157, %i33
  %add162 = add nsw i32 12, %i.0
  %idxprom163 = sext i32 %add162 to i64
  %arrayidx164 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom163
  %i34 = load double, double* %arrayidx164, align 8
  %add165 = fadd double %add161, %i34
  %add166 = add nsw i32 13, %i.0
  %idxprom167 = sext i32 %add166 to i64
  %arrayidx168 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom167
  %i35 = load double, double* %arrayidx168, align 8
  %add169 = fadd double %add165, %i35
  %add170 = add nsw i32 14, %i.0
  %idxprom171 = sext i32 %add170 to i64
  %arrayidx172 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom171
  %i36 = load double, double* %arrayidx172, align 8
  %add173 = fadd double %add169, %i36
  %add174 = add nsw i32 15, %i.0
  %idxprom175 = sext i32 %add174 to i64
  %arrayidx176 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom175
  %i37 = load double, double* %arrayidx176, align 8
  %add177 = fadd double %add173, %i37
  %add178 = add nsw i32 16, %i.0
  %idxprom179 = sext i32 %add178 to i64
  %arrayidx180 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom179
  %i38 = load double, double* %arrayidx180, align 8
  %add181 = fadd double %add177, %i38
  %add182 = add nsw i32 17, %i.0
  %idxprom183 = sext i32 %add182 to i64
  %arrayidx184 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom183
  %i39 = load double, double* %arrayidx184, align 8
  %add185 = fadd double %add181, %i39
  %add186 = add nsw i32 18, %i.0
  %idxprom187 = sext i32 %add186 to i64
  %arrayidx188 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom187
  %i40 = load double, double* %arrayidx188, align 8
  %add189 = fadd double %add185, %i40
  %add190 = add nsw i32 3, %i.0
  %idxprom191 = sext i32 %add190 to i64
  %arrayidx192 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom191
  %i41 = load double, double* %arrayidx192, align 8
  %add193 = add nsw i32 4, %i.0
  %idxprom194 = sext i32 %add193 to i64
  %arrayidx195 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom194
  %i42 = load double, double* %arrayidx195, align 8
  %sub = fsub double %i41, %i42
  %add196 = add nsw i32 7, %i.0
  %idxprom197 = sext i32 %add196 to i64
  %arrayidx198 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom197
  %i43 = load double, double* %arrayidx198, align 8
  %add199 = fadd double %sub, %i43
  %add200 = add nsw i32 8, %i.0
  %idxprom201 = sext i32 %add200 to i64
  %arrayidx202 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom201
  %i44 = load double, double* %arrayidx202, align 8
  %sub203 = fsub double %add199, %i44
  %add204 = add nsw i32 9, %i.0
  %idxprom205 = sext i32 %add204 to i64
  %arrayidx206 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom205
  %i45 = load double, double* %arrayidx206, align 8
  %add207 = fadd double %sub203, %i45
  %add208 = add nsw i32 10, %i.0
  %idxprom209 = sext i32 %add208 to i64
  %arrayidx210 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom209
  %i46 = load double, double* %arrayidx210, align 8
  %sub211 = fsub double %add207, %i46
  %add212 = add nsw i32 15, %i.0
  %idxprom213 = sext i32 %add212 to i64
  %arrayidx214 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom213
  %i47 = load double, double* %arrayidx214, align 8
  %add215 = fadd double %sub211, %i47
  %add216 = add nsw i32 16, %i.0
  %idxprom217 = sext i32 %add216 to i64
  %arrayidx218 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom217
  %i48 = load double, double* %arrayidx218, align 8
  %add219 = fadd double %add215, %i48
  %add220 = add nsw i32 17, %i.0
  %idxprom221 = sext i32 %add220 to i64
  %arrayidx222 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom221
  %i49 = load double, double* %arrayidx222, align 8
  %sub223 = fsub double %add219, %i49
  %add224 = add nsw i32 18, %i.0
  %idxprom225 = sext i32 %add224 to i64
  %arrayidx226 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom225
  %i50 = load double, double* %arrayidx226, align 8
  %sub227 = fsub double %sub223, %i50
  %add228 = add nsw i32 1, %i.0
  %idxprom229 = sext i32 %add228 to i64
  %arrayidx230 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom229
  %i51 = load double, double* %arrayidx230, align 8
  %add231 = add nsw i32 2, %i.0
  %idxprom232 = sext i32 %add231 to i64
  %arrayidx233 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom232
  %i52 = load double, double* %arrayidx233, align 8
  %sub234 = fsub double %i51, %i52
  %add235 = add nsw i32 7, %i.0
  %idxprom236 = sext i32 %add235 to i64
  %arrayidx237 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom236
  %i53 = load double, double* %arrayidx237, align 8
  %add238 = fadd double %sub234, %i53
  %add239 = add nsw i32 8, %i.0
  %idxprom240 = sext i32 %add239 to i64
  %arrayidx241 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom240
  %i54 = load double, double* %arrayidx241, align 8
  %add242 = fadd double %add238, %i54
  %add243 = add nsw i32 9, %i.0
  %idxprom244 = sext i32 %add243 to i64
  %arrayidx245 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom244
  %i55 = load double, double* %arrayidx245, align 8
  %sub246 = fsub double %add242, %i55
  %add247 = add nsw i32 10, %i.0
  %idxprom248 = sext i32 %add247 to i64
  %arrayidx249 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom248
  %i56 = load double, double* %arrayidx249, align 8
  %sub250 = fsub double %sub246, %i56
  %add251 = add nsw i32 11, %i.0
  %idxprom252 = sext i32 %add251 to i64
  %arrayidx253 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom252
  %i57 = load double, double* %arrayidx253, align 8
  %add254 = fadd double %sub250, %i57
  %add255 = add nsw i32 12, %i.0
  %idxprom256 = sext i32 %add255 to i64
  %arrayidx257 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom256
  %i58 = load double, double* %arrayidx257, align 8
  %add258 = fadd double %add254, %i58
  %add259 = add nsw i32 13, %i.0
  %idxprom260 = sext i32 %add259 to i64
  %arrayidx261 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom260
  %i59 = load double, double* %arrayidx261, align 8
  %sub262 = fsub double %add258, %i59
  %add263 = add nsw i32 14, %i.0
  %idxprom264 = sext i32 %add263 to i64
  %arrayidx265 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom264
  %i60 = load double, double* %arrayidx265, align 8
  %sub266 = fsub double %sub262, %i60
  %add267 = add nsw i32 5, %i.0
  %idxprom268 = sext i32 %add267 to i64
  %arrayidx269 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom268
  %i61 = load double, double* %arrayidx269, align 8
  %add270 = add nsw i32 6, %i.0
  %idxprom271 = sext i32 %add270 to i64
  %arrayidx272 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom271
  %i62 = load double, double* %arrayidx272, align 8
  %sub273 = fsub double %i61, %i62
  %add274 = add nsw i32 11, %i.0
  %idxprom275 = sext i32 %add274 to i64
  %arrayidx276 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom275
  %i63 = load double, double* %arrayidx276, align 8
  %add277 = fadd double %sub273, %i63
  %add278 = add nsw i32 12, %i.0
  %idxprom279 = sext i32 %add278 to i64
  %arrayidx280 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom279
  %i64 = load double, double* %arrayidx280, align 8
  %sub281 = fsub double %add277, %i64
  %add282 = add nsw i32 13, %i.0
  %idxprom283 = sext i32 %add282 to i64
  %arrayidx284 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom283
  %i65 = load double, double* %arrayidx284, align 8
  %add285 = fadd double %sub281, %i65
  %add286 = add nsw i32 14, %i.0
  %idxprom287 = sext i32 %add286 to i64
  %arrayidx288 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom287
  %i66 = load double, double* %arrayidx288, align 8
  %sub289 = fsub double %add285, %i66
  %add290 = add nsw i32 15, %i.0
  %idxprom291 = sext i32 %add290 to i64
  %arrayidx292 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom291
  %i67 = load double, double* %arrayidx292, align 8
  %add293 = fadd double %sub289, %i67
  %add294 = add nsw i32 16, %i.0
  %idxprom295 = sext i32 %add294 to i64
  %arrayidx296 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom295
  %i68 = load double, double* %arrayidx296, align 8
  %sub297 = fsub double %add293, %i68
  %add298 = add nsw i32 17, %i.0
  %idxprom299 = sext i32 %add298 to i64
  %arrayidx300 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom299
  %i69 = load double, double* %arrayidx300, align 8
  %add301 = fadd double %sub297, %i69
  %add302 = add nsw i32 18, %i.0
  %idxprom303 = sext i32 %add302 to i64
  %arrayidx304 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom303
  %i70 = load double, double* %arrayidx304, align 8
  %sub305 = fsub double %add301, %i70
  %div = fdiv double %sub227, %add189
  %div306 = fdiv double %sub266, %add189
  %div307 = fdiv double %sub305, %add189
  %add308 = add nsw i32 19, %i.0
  %idxprom309 = sext i32 %add308 to i64
  %arrayidx310 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom309
  %i71 = bitcast double* %arrayidx310 to i8*
  %i72 = bitcast i8* %i71 to i32*
  %i73 = load i32, i32* %i72, align 4
  %and311 = and i32 %i73, 2
  %tobool312 = icmp ne i32 %and311, 0
  br i1 %tobool312, label %if.then313, label %if.end314

if.then313:                                       ; preds = %if.end
  br label %if.end314

if.end314:                                        ; preds = %if.then313, %if.end
  %ux.0 = phi double [ 5.000000e-03, %if.then313 ], [ %div, %if.end ]
  %uy.0 = phi double [ 2.000000e-03, %if.then313 ], [ %div306, %if.end ]
  %uz.0 = phi double [ 0.000000e+00, %if.then313 ], [ %div307, %if.end ]
  %mul = fmul double %ux.0, %ux.0
  %mul315 = fmul double %uy.0, %uy.0
  %add316 = fadd double %mul, %mul315
  %mul317 = fmul double %uz.0, %uz.0
  %add318 = fadd double %add316, %mul317
  %mul319 = fmul double 1.500000e+00, %add318
  %add320 = add nsw i32 0, %i.0
  %idxprom321 = sext i32 %add320 to i64
  %arrayidx322 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom321
  %i74 = load double, double* %arrayidx322, align 8
  %mul323 = fmul double 0xBFEE666666666666, %i74
  %mul324 = fmul double 0x3FE4CCCCCCCCCCCC, %add189
  %sub325 = fsub double 1.000000e+00, %mul319
  %mul326 = fmul double %mul324, %sub325
  %add327 = fadd double %mul323, %mul326
  %add328 = add nsw i32 0, %i.0
  %idxprom329 = sext i32 %add328 to i64
  %arrayidx330 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom329
  store double %add327, double* %arrayidx330, align 8
  %add331 = add nsw i32 1, %i.0
  %idxprom332 = sext i32 %add331 to i64
  %arrayidx333 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom332
  %i75 = load double, double* %arrayidx333, align 8
  %mul334 = fmul double 0xBFEE666666666666, %i75
  %mul335 = fmul double 0x3FBBBBBBBBBBBBBB, %add189
  %mul336 = fmul double 4.500000e+00, %uy.0
  %add337 = fadd double %mul336, 3.000000e+00
  %mul338 = fmul double %uy.0, %add337
  %add339 = fadd double 1.000000e+00, %mul338
  %sub340 = fsub double %add339, %mul319
  %mul341 = fmul double %mul335, %sub340
  %add342 = fadd double %mul334, %mul341
  %add343 = add nsw i32 2001, %i.0
  %idxprom344 = sext i32 %add343 to i64
  %arrayidx345 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom344
  store double %add342, double* %arrayidx345, align 8
  %add346 = add nsw i32 2, %i.0
  %idxprom347 = sext i32 %add346 to i64
  %arrayidx348 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom347
  %i76 = load double, double* %arrayidx348, align 8
  %mul349 = fmul double 0xBFEE666666666666, %i76
  %mul350 = fmul double 0x3FBBBBBBBBBBBBBB, %add189
  %mul351 = fmul double 4.500000e+00, %uy.0
  %sub352 = fsub double %mul351, 3.000000e+00
  %mul353 = fmul double %uy.0, %sub352
  %add354 = fadd double 1.000000e+00, %mul353
  %sub355 = fsub double %add354, %mul319
  %mul356 = fmul double %mul350, %sub355
  %add357 = fadd double %mul349, %mul356
  %add358 = add nsw i32 -1998, %i.0
  %idxprom359 = sext i32 %add358 to i64
  %arrayidx360 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom359
  store double %add357, double* %arrayidx360, align 8
  %add361 = add nsw i32 3, %i.0
  %idxprom362 = sext i32 %add361 to i64
  %arrayidx363 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom362
  %i77 = load double, double* %arrayidx363, align 8
  %mul364 = fmul double 0xBFEE666666666666, %i77
  %mul365 = fmul double 0x3FBBBBBBBBBBBBBB, %add189
  %mul366 = fmul double 4.500000e+00, %ux.0
  %add367 = fadd double %mul366, 3.000000e+00
  %mul368 = fmul double %ux.0, %add367
  %add369 = fadd double 1.000000e+00, %mul368
  %sub370 = fsub double %add369, %mul319
  %mul371 = fmul double %mul365, %sub370
  %add372 = fadd double %mul364, %mul371
  %add373 = add nsw i32 23, %i.0
  %idxprom374 = sext i32 %add373 to i64
  %arrayidx375 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom374
  store double %add372, double* %arrayidx375, align 8
  %add376 = add nsw i32 4, %i.0
  %idxprom377 = sext i32 %add376 to i64
  %arrayidx378 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom377
  %i78 = load double, double* %arrayidx378, align 8
  %mul379 = fmul double 0xBFEE666666666666, %i78
  %mul380 = fmul double 0x3FBBBBBBBBBBBBBB, %add189
  %mul381 = fmul double 4.500000e+00, %ux.0
  %sub382 = fsub double %mul381, 3.000000e+00
  %mul383 = fmul double %ux.0, %sub382
  %add384 = fadd double 1.000000e+00, %mul383
  %sub385 = fsub double %add384, %mul319
  %mul386 = fmul double %mul380, %sub385
  %add387 = fadd double %mul379, %mul386
  %add388 = add nsw i32 -16, %i.0
  %idxprom389 = sext i32 %add388 to i64
  %arrayidx390 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom389
  store double %add387, double* %arrayidx390, align 8
  %add391 = add nsw i32 5, %i.0
  %idxprom392 = sext i32 %add391 to i64
  %arrayidx393 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom392
  %i79 = load double, double* %arrayidx393, align 8
  %mul394 = fmul double 0xBFEE666666666666, %i79
  %mul395 = fmul double 0x3FBBBBBBBBBBBBBB, %add189
  %mul396 = fmul double 4.500000e+00, %uz.0
  %add397 = fadd double %mul396, 3.000000e+00
  %mul398 = fmul double %uz.0, %add397
  %add399 = fadd double 1.000000e+00, %mul398
  %sub400 = fsub double %add399, %mul319
  %mul401 = fmul double %mul395, %sub400
  %add402 = fadd double %mul394, %mul401
  %add403 = add nsw i32 200005, %i.0
  %idxprom404 = sext i32 %add403 to i64
  %arrayidx405 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom404
  store double %add402, double* %arrayidx405, align 8
  %add406 = add nsw i32 6, %i.0
  %idxprom407 = sext i32 %add406 to i64
  %arrayidx408 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom407
  %i80 = load double, double* %arrayidx408, align 8
  %mul409 = fmul double 0xBFEE666666666666, %i80
  %mul410 = fmul double 0x3FBBBBBBBBBBBBBB, %add189
  %mul411 = fmul double 4.500000e+00, %uz.0
  %sub412 = fsub double %mul411, 3.000000e+00
  %mul413 = fmul double %uz.0, %sub412
  %add414 = fadd double 1.000000e+00, %mul413
  %sub415 = fsub double %add414, %mul319
  %mul416 = fmul double %mul410, %sub415
  %add417 = fadd double %mul409, %mul416
  %add418 = add nsw i32 -199994, %i.0
  %idxprom419 = sext i32 %add418 to i64
  %arrayidx420 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom419
  store double %add417, double* %arrayidx420, align 8
  %add421 = add nsw i32 7, %i.0
  %idxprom422 = sext i32 %add421 to i64
  %arrayidx423 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom422
  %i81 = load double, double* %arrayidx423, align 8
  %mul424 = fmul double 0xBFEE666666666666, %i81
  %mul425 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %add426 = fadd double %ux.0, %uy.0
  %add427 = fadd double %ux.0, %uy.0
  %mul428 = fmul double 4.500000e+00, %add427
  %add429 = fadd double %mul428, 3.000000e+00
  %mul430 = fmul double %add426, %add429
  %add431 = fadd double 1.000000e+00, %mul430
  %sub432 = fsub double %add431, %mul319
  %mul433 = fmul double %mul425, %sub432
  %add434 = fadd double %mul424, %mul433
  %add435 = add nsw i32 2027, %i.0
  %idxprom436 = sext i32 %add435 to i64
  %arrayidx437 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom436
  store double %add434, double* %arrayidx437, align 8
  %add438 = add nsw i32 8, %i.0
  %idxprom439 = sext i32 %add438 to i64
  %arrayidx440 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom439
  %i82 = load double, double* %arrayidx440, align 8
  %mul441 = fmul double 0xBFEE666666666666, %i82
  %mul442 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %fneg = fneg double %ux.0
  %add443 = fadd double %fneg, %uy.0
  %fneg444 = fneg double %ux.0
  %add445 = fadd double %fneg444, %uy.0
  %mul446 = fmul double 4.500000e+00, %add445
  %add447 = fadd double %mul446, 3.000000e+00
  %mul448 = fmul double %add443, %add447
  %add449 = fadd double 1.000000e+00, %mul448
  %sub450 = fsub double %add449, %mul319
  %mul451 = fmul double %mul442, %sub450
  %add452 = fadd double %mul441, %mul451
  %add453 = add nsw i32 1988, %i.0
  %idxprom454 = sext i32 %add453 to i64
  %arrayidx455 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom454
  store double %add452, double* %arrayidx455, align 8
  %add456 = add nsw i32 9, %i.0
  %idxprom457 = sext i32 %add456 to i64
  %arrayidx458 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom457
  %i83 = load double, double* %arrayidx458, align 8
  %mul459 = fmul double 0xBFEE666666666666, %i83
  %mul460 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %sub461 = fsub double %ux.0, %uy.0
  %sub462 = fsub double %ux.0, %uy.0
  %mul463 = fmul double 4.500000e+00, %sub462
  %add464 = fadd double %mul463, 3.000000e+00
  %mul465 = fmul double %sub461, %add464
  %add466 = fadd double 1.000000e+00, %mul465
  %sub467 = fsub double %add466, %mul319
  %mul468 = fmul double %mul460, %sub467
  %add469 = fadd double %mul459, %mul468
  %add470 = add nsw i32 -1971, %i.0
  %idxprom471 = sext i32 %add470 to i64
  %arrayidx472 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom471
  store double %add469, double* %arrayidx472, align 8
  %add473 = add nsw i32 10, %i.0
  %idxprom474 = sext i32 %add473 to i64
  %arrayidx475 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom474
  %i84 = load double, double* %arrayidx475, align 8
  %mul476 = fmul double 0xBFEE666666666666, %i84
  %mul477 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %fneg478 = fneg double %ux.0
  %sub479 = fsub double %fneg478, %uy.0
  %fneg480 = fneg double %ux.0
  %sub481 = fsub double %fneg480, %uy.0
  %mul482 = fmul double 4.500000e+00, %sub481
  %add483 = fadd double %mul482, 3.000000e+00
  %mul484 = fmul double %sub479, %add483
  %add485 = fadd double 1.000000e+00, %mul484
  %sub486 = fsub double %add485, %mul319
  %mul487 = fmul double %mul477, %sub486
  %add488 = fadd double %mul476, %mul487
  %add489 = add nsw i32 -2010, %i.0
  %idxprom490 = sext i32 %add489 to i64
  %arrayidx491 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom490
  store double %add488, double* %arrayidx491, align 8
  %add492 = add nsw i32 11, %i.0
  %idxprom493 = sext i32 %add492 to i64
  %arrayidx494 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom493
  %i85 = load double, double* %arrayidx494, align 8
  %mul495 = fmul double 0xBFEE666666666666, %i85
  %mul496 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %add497 = fadd double %uy.0, %uz.0
  %add498 = fadd double %uy.0, %uz.0
  %mul499 = fmul double 4.500000e+00, %add498
  %add500 = fadd double %mul499, 3.000000e+00
  %mul501 = fmul double %add497, %add500
  %add502 = fadd double 1.000000e+00, %mul501
  %sub503 = fsub double %add502, %mul319
  %mul504 = fmul double %mul496, %sub503
  %add505 = fadd double %mul495, %mul504
  %add506 = add nsw i32 202011, %i.0
  %idxprom507 = sext i32 %add506 to i64
  %arrayidx508 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom507
  store double %add505, double* %arrayidx508, align 8
  %add509 = add nsw i32 12, %i.0
  %idxprom510 = sext i32 %add509 to i64
  %arrayidx511 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom510
  %i86 = load double, double* %arrayidx511, align 8
  %mul512 = fmul double 0xBFEE666666666666, %i86
  %mul513 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %sub514 = fsub double %uy.0, %uz.0
  %sub515 = fsub double %uy.0, %uz.0
  %mul516 = fmul double 4.500000e+00, %sub515
  %add517 = fadd double %mul516, 3.000000e+00
  %mul518 = fmul double %sub514, %add517
  %add519 = fadd double 1.000000e+00, %mul518
  %sub520 = fsub double %add519, %mul319
  %mul521 = fmul double %mul513, %sub520
  %add522 = fadd double %mul512, %mul521
  %add523 = add nsw i32 -197988, %i.0
  %idxprom524 = sext i32 %add523 to i64
  %arrayidx525 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom524
  store double %add522, double* %arrayidx525, align 8
  %add526 = add nsw i32 13, %i.0
  %idxprom527 = sext i32 %add526 to i64
  %arrayidx528 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom527
  %i87 = load double, double* %arrayidx528, align 8
  %mul529 = fmul double 0xBFEE666666666666, %i87
  %mul530 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %fneg531 = fneg double %uy.0
  %add532 = fadd double %fneg531, %uz.0
  %fneg533 = fneg double %uy.0
  %add534 = fadd double %fneg533, %uz.0
  %mul535 = fmul double 4.500000e+00, %add534
  %add536 = fadd double %mul535, 3.000000e+00
  %mul537 = fmul double %add532, %add536
  %add538 = fadd double 1.000000e+00, %mul537
  %sub539 = fsub double %add538, %mul319
  %mul540 = fmul double %mul530, %sub539
  %add541 = fadd double %mul529, %mul540
  %add542 = add nsw i32 198013, %i.0
  %idxprom543 = sext i32 %add542 to i64
  %arrayidx544 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom543
  store double %add541, double* %arrayidx544, align 8
  %add545 = add nsw i32 14, %i.0
  %idxprom546 = sext i32 %add545 to i64
  %arrayidx547 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom546
  %i88 = load double, double* %arrayidx547, align 8
  %mul548 = fmul double 0xBFEE666666666666, %i88
  %mul549 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %fneg550 = fneg double %uy.0
  %sub551 = fsub double %fneg550, %uz.0
  %fneg552 = fneg double %uy.0
  %sub553 = fsub double %fneg552, %uz.0
  %mul554 = fmul double 4.500000e+00, %sub553
  %add555 = fadd double %mul554, 3.000000e+00
  %mul556 = fmul double %sub551, %add555
  %add557 = fadd double 1.000000e+00, %mul556
  %sub558 = fsub double %add557, %mul319
  %mul559 = fmul double %mul549, %sub558
  %add560 = fadd double %mul548, %mul559
  %add561 = add nsw i32 -201986, %i.0
  %idxprom562 = sext i32 %add561 to i64
  %arrayidx563 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom562
  store double %add560, double* %arrayidx563, align 8
  %add564 = add nsw i32 15, %i.0
  %idxprom565 = sext i32 %add564 to i64
  %arrayidx566 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom565
  %i89 = load double, double* %arrayidx566, align 8
  %mul567 = fmul double 0xBFEE666666666666, %i89
  %mul568 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %add569 = fadd double %ux.0, %uz.0
  %add570 = fadd double %ux.0, %uz.0
  %mul571 = fmul double 4.500000e+00, %add570
  %add572 = fadd double %mul571, 3.000000e+00
  %mul573 = fmul double %add569, %add572
  %add574 = fadd double 1.000000e+00, %mul573
  %sub575 = fsub double %add574, %mul319
  %mul576 = fmul double %mul568, %sub575
  %add577 = fadd double %mul567, %mul576
  %add578 = add nsw i32 200035, %i.0
  %idxprom579 = sext i32 %add578 to i64
  %arrayidx580 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom579
  store double %add577, double* %arrayidx580, align 8
  %add581 = add nsw i32 16, %i.0
  %idxprom582 = sext i32 %add581 to i64
  %arrayidx583 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom582
  %i90 = load double, double* %arrayidx583, align 8
  %mul584 = fmul double 0xBFEE666666666666, %i90
  %mul585 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %sub586 = fsub double %ux.0, %uz.0
  %sub587 = fsub double %ux.0, %uz.0
  %mul588 = fmul double 4.500000e+00, %sub587
  %add589 = fadd double %mul588, 3.000000e+00
  %mul590 = fmul double %sub586, %add589
  %add591 = fadd double 1.000000e+00, %mul590
  %sub592 = fsub double %add591, %mul319
  %mul593 = fmul double %mul585, %sub592
  %add594 = fadd double %mul584, %mul593
  %add595 = add nsw i32 -199964, %i.0
  %idxprom596 = sext i32 %add595 to i64
  %arrayidx597 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom596
  store double %add594, double* %arrayidx597, align 8
  %add598 = add nsw i32 17, %i.0
  %idxprom599 = sext i32 %add598 to i64
  %arrayidx600 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom599
  %i91 = load double, double* %arrayidx600, align 8
  %mul601 = fmul double 0xBFEE666666666666, %i91
  %mul602 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %fneg603 = fneg double %ux.0
  %add604 = fadd double %fneg603, %uz.0
  %fneg605 = fneg double %ux.0
  %add606 = fadd double %fneg605, %uz.0
  %mul607 = fmul double 4.500000e+00, %add606
  %add608 = fadd double %mul607, 3.000000e+00
  %mul609 = fmul double %add604, %add608
  %add610 = fadd double 1.000000e+00, %mul609
  %sub611 = fsub double %add610, %mul319
  %mul612 = fmul double %mul602, %sub611
  %add613 = fadd double %mul601, %mul612
  %add614 = add nsw i32 199997, %i.0
  %idxprom615 = sext i32 %add614 to i64
  %arrayidx616 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom615
  store double %add613, double* %arrayidx616, align 8
  %add617 = add nsw i32 18, %i.0
  %idxprom618 = sext i32 %add617 to i64
  %arrayidx619 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom618
  %i92 = load double, double* %arrayidx619, align 8
  %mul620 = fmul double 0xBFEE666666666666, %i92
  %mul621 = fmul double 0x3FABBBBBBBBBBBBB, %add189
  %fneg622 = fneg double %ux.0
  %sub623 = fsub double %fneg622, %uz.0
  %fneg624 = fneg double %ux.0
  %sub625 = fsub double %fneg624, %uz.0
  %mul626 = fmul double 4.500000e+00, %sub625
  %add627 = fadd double %mul626, 3.000000e+00
  %mul628 = fmul double %sub623, %add627
  %add629 = fadd double 1.000000e+00, %mul628
  %sub630 = fsub double %add629, %mul319
  %mul631 = fmul double %mul621, %sub630
  %add632 = fadd double %mul620, %mul631
  %add633 = add nsw i32 -200002, %i.0
  %idxprom634 = sext i32 %add633 to i64
  %arrayidx635 = getelementptr inbounds double, double* %dstGrid, i64 %idxprom634
  store double %add632, double* %arrayidx635, align 8
  br label %for.inc

for.inc:                                          ; preds = %if.end314, %if.then
  %add636 = add nsw i32 %i.0, 20
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_handleInOutFlow(double* %srcGrid) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %add389, %for.inc ]
  %cmp = icmp slt i32 %i.0, 200000
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %add = add nsw i32 200000, %i.0
  %idxprom = sext i32 %add to i64
  %arrayidx = getelementptr inbounds double, double* %srcGrid, i64 %idxprom
  %i = load double, double* %arrayidx, align 8
  %add1 = add nsw i32 200001, %i.0
  %idxprom2 = sext i32 %add1 to i64
  %arrayidx3 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom2
  %i1 = load double, double* %arrayidx3, align 8
  %add4 = fadd double %i, %i1
  %add5 = add nsw i32 200002, %i.0
  %idxprom6 = sext i32 %add5 to i64
  %arrayidx7 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom6
  %i2 = load double, double* %arrayidx7, align 8
  %add8 = fadd double %add4, %i2
  %add9 = add nsw i32 200003, %i.0
  %idxprom10 = sext i32 %add9 to i64
  %arrayidx11 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom10
  %i3 = load double, double* %arrayidx11, align 8
  %add12 = fadd double %add8, %i3
  %add13 = add nsw i32 200004, %i.0
  %idxprom14 = sext i32 %add13 to i64
  %arrayidx15 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom14
  %i4 = load double, double* %arrayidx15, align 8
  %add16 = fadd double %add12, %i4
  %add17 = add nsw i32 200005, %i.0
  %idxprom18 = sext i32 %add17 to i64
  %arrayidx19 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom18
  %i5 = load double, double* %arrayidx19, align 8
  %add20 = fadd double %add16, %i5
  %add21 = add nsw i32 200006, %i.0
  %idxprom22 = sext i32 %add21 to i64
  %arrayidx23 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom22
  %i6 = load double, double* %arrayidx23, align 8
  %add24 = fadd double %add20, %i6
  %add25 = add nsw i32 200007, %i.0
  %idxprom26 = sext i32 %add25 to i64
  %arrayidx27 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom26
  %i7 = load double, double* %arrayidx27, align 8
  %add28 = fadd double %add24, %i7
  %add29 = add nsw i32 200008, %i.0
  %idxprom30 = sext i32 %add29 to i64
  %arrayidx31 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom30
  %i8 = load double, double* %arrayidx31, align 8
  %add32 = fadd double %add28, %i8
  %add33 = add nsw i32 200009, %i.0
  %idxprom34 = sext i32 %add33 to i64
  %arrayidx35 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom34
  %i9 = load double, double* %arrayidx35, align 8
  %add36 = fadd double %add32, %i9
  %add37 = add nsw i32 200010, %i.0
  %idxprom38 = sext i32 %add37 to i64
  %arrayidx39 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom38
  %i10 = load double, double* %arrayidx39, align 8
  %add40 = fadd double %add36, %i10
  %add41 = add nsw i32 200011, %i.0
  %idxprom42 = sext i32 %add41 to i64
  %arrayidx43 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom42
  %i11 = load double, double* %arrayidx43, align 8
  %add44 = fadd double %add40, %i11
  %add45 = add nsw i32 200012, %i.0
  %idxprom46 = sext i32 %add45 to i64
  %arrayidx47 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom46
  %i12 = load double, double* %arrayidx47, align 8
  %add48 = fadd double %add44, %i12
  %add49 = add nsw i32 200013, %i.0
  %idxprom50 = sext i32 %add49 to i64
  %arrayidx51 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom50
  %i13 = load double, double* %arrayidx51, align 8
  %add52 = fadd double %add48, %i13
  %add53 = add nsw i32 200014, %i.0
  %idxprom54 = sext i32 %add53 to i64
  %arrayidx55 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom54
  %i14 = load double, double* %arrayidx55, align 8
  %add56 = fadd double %add52, %i14
  %add57 = add nsw i32 200015, %i.0
  %idxprom58 = sext i32 %add57 to i64
  %arrayidx59 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom58
  %i15 = load double, double* %arrayidx59, align 8
  %add60 = fadd double %add56, %i15
  %add61 = add nsw i32 200016, %i.0
  %idxprom62 = sext i32 %add61 to i64
  %arrayidx63 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom62
  %i16 = load double, double* %arrayidx63, align 8
  %add64 = fadd double %add60, %i16
  %add65 = add nsw i32 200017, %i.0
  %idxprom66 = sext i32 %add65 to i64
  %arrayidx67 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom66
  %i17 = load double, double* %arrayidx67, align 8
  %add68 = fadd double %add64, %i17
  %add69 = add nsw i32 200018, %i.0
  %idxprom70 = sext i32 %add69 to i64
  %arrayidx71 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom70
  %i18 = load double, double* %arrayidx71, align 8
  %add72 = fadd double %add68, %i18
  %add73 = add nsw i32 400000, %i.0
  %idxprom74 = sext i32 %add73 to i64
  %arrayidx75 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom74
  %i19 = load double, double* %arrayidx75, align 8
  %add76 = add nsw i32 400001, %i.0
  %idxprom77 = sext i32 %add76 to i64
  %arrayidx78 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom77
  %i20 = load double, double* %arrayidx78, align 8
  %add79 = fadd double %i19, %i20
  %add80 = add nsw i32 400002, %i.0
  %idxprom81 = sext i32 %add80 to i64
  %arrayidx82 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom81
  %i21 = load double, double* %arrayidx82, align 8
  %add83 = fadd double %add79, %i21
  %add84 = add nsw i32 400003, %i.0
  %idxprom85 = sext i32 %add84 to i64
  %arrayidx86 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom85
  %i22 = load double, double* %arrayidx86, align 8
  %add87 = fadd double %add83, %i22
  %add88 = add nsw i32 400004, %i.0
  %idxprom89 = sext i32 %add88 to i64
  %arrayidx90 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom89
  %i23 = load double, double* %arrayidx90, align 8
  %add91 = fadd double %add87, %i23
  %add92 = add nsw i32 400005, %i.0
  %idxprom93 = sext i32 %add92 to i64
  %arrayidx94 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom93
  %i24 = load double, double* %arrayidx94, align 8
  %add95 = fadd double %add91, %i24
  %add96 = add nsw i32 400006, %i.0
  %idxprom97 = sext i32 %add96 to i64
  %arrayidx98 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom97
  %i25 = load double, double* %arrayidx98, align 8
  %add99 = fadd double %add95, %i25
  %add100 = add nsw i32 400007, %i.0
  %idxprom101 = sext i32 %add100 to i64
  %arrayidx102 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom101
  %i26 = load double, double* %arrayidx102, align 8
  %add103 = fadd double %add99, %i26
  %add104 = add nsw i32 400008, %i.0
  %idxprom105 = sext i32 %add104 to i64
  %arrayidx106 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom105
  %i27 = load double, double* %arrayidx106, align 8
  %add107 = fadd double %add103, %i27
  %add108 = add nsw i32 400009, %i.0
  %idxprom109 = sext i32 %add108 to i64
  %arrayidx110 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom109
  %i28 = load double, double* %arrayidx110, align 8
  %add111 = fadd double %add107, %i28
  %add112 = add nsw i32 400010, %i.0
  %idxprom113 = sext i32 %add112 to i64
  %arrayidx114 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom113
  %i29 = load double, double* %arrayidx114, align 8
  %add115 = fadd double %add111, %i29
  %add116 = add nsw i32 400011, %i.0
  %idxprom117 = sext i32 %add116 to i64
  %arrayidx118 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom117
  %i30 = load double, double* %arrayidx118, align 8
  %add119 = fadd double %add115, %i30
  %add120 = add nsw i32 400012, %i.0
  %idxprom121 = sext i32 %add120 to i64
  %arrayidx122 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom121
  %i31 = load double, double* %arrayidx122, align 8
  %add123 = fadd double %add119, %i31
  %add124 = add nsw i32 400013, %i.0
  %idxprom125 = sext i32 %add124 to i64
  %arrayidx126 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom125
  %i32 = load double, double* %arrayidx126, align 8
  %add127 = fadd double %add123, %i32
  %add128 = add nsw i32 400014, %i.0
  %idxprom129 = sext i32 %add128 to i64
  %arrayidx130 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom129
  %i33 = load double, double* %arrayidx130, align 8
  %add131 = fadd double %add127, %i33
  %add132 = add nsw i32 400015, %i.0
  %idxprom133 = sext i32 %add132 to i64
  %arrayidx134 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom133
  %i34 = load double, double* %arrayidx134, align 8
  %add135 = fadd double %add131, %i34
  %add136 = add nsw i32 400016, %i.0
  %idxprom137 = sext i32 %add136 to i64
  %arrayidx138 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom137
  %i35 = load double, double* %arrayidx138, align 8
  %add139 = fadd double %add135, %i35
  %add140 = add nsw i32 400017, %i.0
  %idxprom141 = sext i32 %add140 to i64
  %arrayidx142 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom141
  %i36 = load double, double* %arrayidx142, align 8
  %add143 = fadd double %add139, %i36
  %add144 = add nsw i32 400018, %i.0
  %idxprom145 = sext i32 %add144 to i64
  %arrayidx146 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom145
  %i37 = load double, double* %arrayidx146, align 8
  %add147 = fadd double %add143, %i37
  %mul = fmul double 2.000000e+00, %add72
  %sub = fsub double %mul, %add147
  %div = sdiv i32 %i.0, 20
  %rem = srem i32 %div, 100
  %conv = sitofp i32 %rem to double
  %div148 = fdiv double %conv, 4.950000e+01
  %sub149 = fsub double %div148, 1.000000e+00
  %div150 = sdiv i32 %i.0, 20
  %div151 = sdiv i32 %div150, 100
  %rem152 = srem i32 %div151, 100
  %conv153 = sitofp i32 %rem152 to double
  %div154 = fdiv double %conv153, 4.950000e+01
  %sub155 = fsub double %div154, 1.000000e+00
  %mul156 = fmul double %sub149, %sub149
  %sub157 = fsub double 1.000000e+00, %mul156
  %mul158 = fmul double 1.000000e-02, %sub157
  %mul159 = fmul double %sub155, %sub155
  %sub160 = fsub double 1.000000e+00, %mul159
  %mul161 = fmul double %mul158, %sub160
  %mul162 = fmul double 0.000000e+00, 0.000000e+00
  %mul163 = fmul double 0.000000e+00, 0.000000e+00
  %add164 = fadd double %mul162, %mul163
  %mul165 = fmul double %mul161, %mul161
  %add166 = fadd double %add164, %mul165
  %mul167 = fmul double 1.500000e+00, %add166
  %mul168 = fmul double 0x3FD5555555555555, %sub
  %sub169 = fsub double 1.000000e+00, %mul167
  %mul170 = fmul double %mul168, %sub169
  %add171 = add nsw i32 0, %i.0
  %idxprom172 = sext i32 %add171 to i64
  %arrayidx173 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom172
  store double %mul170, double* %arrayidx173, align 8
  %mul174 = fmul double 0x3FAC71C71C71C71C, %sub
  %mul175 = fmul double 4.500000e+00, 0.000000e+00
  %add176 = fadd double %mul175, 3.000000e+00
  %mul177 = fmul double 0.000000e+00, %add176
  %add178 = fadd double 1.000000e+00, %mul177
  %sub179 = fsub double %add178, %mul167
  %mul180 = fmul double %mul174, %sub179
  %add181 = add nsw i32 1, %i.0
  %idxprom182 = sext i32 %add181 to i64
  %arrayidx183 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom182
  store double %mul180, double* %arrayidx183, align 8
  %mul184 = fmul double 0x3FAC71C71C71C71C, %sub
  %mul185 = fmul double 4.500000e+00, 0.000000e+00
  %sub186 = fsub double %mul185, 3.000000e+00
  %mul187 = fmul double 0.000000e+00, %sub186
  %add188 = fadd double 1.000000e+00, %mul187
  %sub189 = fsub double %add188, %mul167
  %mul190 = fmul double %mul184, %sub189
  %add191 = add nsw i32 2, %i.0
  %idxprom192 = sext i32 %add191 to i64
  %arrayidx193 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom192
  store double %mul190, double* %arrayidx193, align 8
  %mul194 = fmul double 0x3FAC71C71C71C71C, %sub
  %mul195 = fmul double 4.500000e+00, 0.000000e+00
  %add196 = fadd double %mul195, 3.000000e+00
  %mul197 = fmul double 0.000000e+00, %add196
  %add198 = fadd double 1.000000e+00, %mul197
  %sub199 = fsub double %add198, %mul167
  %mul200 = fmul double %mul194, %sub199
  %add201 = add nsw i32 3, %i.0
  %idxprom202 = sext i32 %add201 to i64
  %arrayidx203 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom202
  store double %mul200, double* %arrayidx203, align 8
  %mul204 = fmul double 0x3FAC71C71C71C71C, %sub
  %mul205 = fmul double 4.500000e+00, 0.000000e+00
  %sub206 = fsub double %mul205, 3.000000e+00
  %mul207 = fmul double 0.000000e+00, %sub206
  %add208 = fadd double 1.000000e+00, %mul207
  %sub209 = fsub double %add208, %mul167
  %mul210 = fmul double %mul204, %sub209
  %add211 = add nsw i32 4, %i.0
  %idxprom212 = sext i32 %add211 to i64
  %arrayidx213 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom212
  store double %mul210, double* %arrayidx213, align 8
  %mul214 = fmul double 0x3FAC71C71C71C71C, %sub
  %mul215 = fmul double 4.500000e+00, %mul161
  %add216 = fadd double %mul215, 3.000000e+00
  %mul217 = fmul double %mul161, %add216
  %add218 = fadd double 1.000000e+00, %mul217
  %sub219 = fsub double %add218, %mul167
  %mul220 = fmul double %mul214, %sub219
  %add221 = add nsw i32 5, %i.0
  %idxprom222 = sext i32 %add221 to i64
  %arrayidx223 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom222
  store double %mul220, double* %arrayidx223, align 8
  %mul224 = fmul double 0x3FAC71C71C71C71C, %sub
  %mul225 = fmul double 4.500000e+00, %mul161
  %sub226 = fsub double %mul225, 3.000000e+00
  %mul227 = fmul double %mul161, %sub226
  %add228 = fadd double 1.000000e+00, %mul227
  %sub229 = fsub double %add228, %mul167
  %mul230 = fmul double %mul224, %sub229
  %add231 = add nsw i32 6, %i.0
  %idxprom232 = sext i32 %add231 to i64
  %arrayidx233 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom232
  store double %mul230, double* %arrayidx233, align 8
  %mul234 = fmul double 0x3F9C71C71C71C71C, %sub
  %add235 = fadd double 0.000000e+00, 0.000000e+00
  %add236 = fadd double 0.000000e+00, 0.000000e+00
  %mul237 = fmul double 4.500000e+00, %add236
  %add238 = fadd double %mul237, 3.000000e+00
  %mul239 = fmul double %add235, %add238
  %add240 = fadd double 1.000000e+00, %mul239
  %sub241 = fsub double %add240, %mul167
  %mul242 = fmul double %mul234, %sub241
  %add243 = add nsw i32 7, %i.0
  %idxprom244 = sext i32 %add243 to i64
  %arrayidx245 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom244
  store double %mul242, double* %arrayidx245, align 8
  %mul246 = fmul double 0x3F9C71C71C71C71C, %sub
  %fneg = fneg double 0.000000e+00
  %add247 = fadd double %fneg, 0.000000e+00
  %fneg248 = fneg double 0.000000e+00
  %add249 = fadd double %fneg248, 0.000000e+00
  %mul250 = fmul double 4.500000e+00, %add249
  %add251 = fadd double %mul250, 3.000000e+00
  %mul252 = fmul double %add247, %add251
  %add253 = fadd double 1.000000e+00, %mul252
  %sub254 = fsub double %add253, %mul167
  %mul255 = fmul double %mul246, %sub254
  %add256 = add nsw i32 8, %i.0
  %idxprom257 = sext i32 %add256 to i64
  %arrayidx258 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom257
  store double %mul255, double* %arrayidx258, align 8
  %mul259 = fmul double 0x3F9C71C71C71C71C, %sub
  %sub260 = fsub double 0.000000e+00, 0.000000e+00
  %sub261 = fsub double 0.000000e+00, 0.000000e+00
  %mul262 = fmul double 4.500000e+00, %sub261
  %add263 = fadd double %mul262, 3.000000e+00
  %mul264 = fmul double %sub260, %add263
  %add265 = fadd double 1.000000e+00, %mul264
  %sub266 = fsub double %add265, %mul167
  %mul267 = fmul double %mul259, %sub266
  %add268 = add nsw i32 9, %i.0
  %idxprom269 = sext i32 %add268 to i64
  %arrayidx270 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom269
  store double %mul267, double* %arrayidx270, align 8
  %mul271 = fmul double 0x3F9C71C71C71C71C, %sub
  %fneg272 = fneg double 0.000000e+00
  %sub273 = fsub double %fneg272, 0.000000e+00
  %fneg274 = fneg double 0.000000e+00
  %sub275 = fsub double %fneg274, 0.000000e+00
  %mul276 = fmul double 4.500000e+00, %sub275
  %add277 = fadd double %mul276, 3.000000e+00
  %mul278 = fmul double %sub273, %add277
  %add279 = fadd double 1.000000e+00, %mul278
  %sub280 = fsub double %add279, %mul167
  %mul281 = fmul double %mul271, %sub280
  %add282 = add nsw i32 10, %i.0
  %idxprom283 = sext i32 %add282 to i64
  %arrayidx284 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom283
  store double %mul281, double* %arrayidx284, align 8
  %mul285 = fmul double 0x3F9C71C71C71C71C, %sub
  %add286 = fadd double 0.000000e+00, %mul161
  %add287 = fadd double 0.000000e+00, %mul161
  %mul288 = fmul double 4.500000e+00, %add287
  %add289 = fadd double %mul288, 3.000000e+00
  %mul290 = fmul double %add286, %add289
  %add291 = fadd double 1.000000e+00, %mul290
  %sub292 = fsub double %add291, %mul167
  %mul293 = fmul double %mul285, %sub292
  %add294 = add nsw i32 11, %i.0
  %idxprom295 = sext i32 %add294 to i64
  %arrayidx296 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom295
  store double %mul293, double* %arrayidx296, align 8
  %mul297 = fmul double 0x3F9C71C71C71C71C, %sub
  %sub298 = fsub double 0.000000e+00, %mul161
  %sub299 = fsub double 0.000000e+00, %mul161
  %mul300 = fmul double 4.500000e+00, %sub299
  %add301 = fadd double %mul300, 3.000000e+00
  %mul302 = fmul double %sub298, %add301
  %add303 = fadd double 1.000000e+00, %mul302
  %sub304 = fsub double %add303, %mul167
  %mul305 = fmul double %mul297, %sub304
  %add306 = add nsw i32 12, %i.0
  %idxprom307 = sext i32 %add306 to i64
  %arrayidx308 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom307
  store double %mul305, double* %arrayidx308, align 8
  %mul309 = fmul double 0x3F9C71C71C71C71C, %sub
  %fneg310 = fneg double 0.000000e+00
  %add311 = fadd double %fneg310, %mul161
  %fneg312 = fneg double 0.000000e+00
  %add313 = fadd double %fneg312, %mul161
  %mul314 = fmul double 4.500000e+00, %add313
  %add315 = fadd double %mul314, 3.000000e+00
  %mul316 = fmul double %add311, %add315
  %add317 = fadd double 1.000000e+00, %mul316
  %sub318 = fsub double %add317, %mul167
  %mul319 = fmul double %mul309, %sub318
  %add320 = add nsw i32 13, %i.0
  %idxprom321 = sext i32 %add320 to i64
  %arrayidx322 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom321
  store double %mul319, double* %arrayidx322, align 8
  %mul323 = fmul double 0x3F9C71C71C71C71C, %sub
  %fneg324 = fneg double 0.000000e+00
  %sub325 = fsub double %fneg324, %mul161
  %fneg326 = fneg double 0.000000e+00
  %sub327 = fsub double %fneg326, %mul161
  %mul328 = fmul double 4.500000e+00, %sub327
  %add329 = fadd double %mul328, 3.000000e+00
  %mul330 = fmul double %sub325, %add329
  %add331 = fadd double 1.000000e+00, %mul330
  %sub332 = fsub double %add331, %mul167
  %mul333 = fmul double %mul323, %sub332
  %add334 = add nsw i32 14, %i.0
  %idxprom335 = sext i32 %add334 to i64
  %arrayidx336 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom335
  store double %mul333, double* %arrayidx336, align 8
  %mul337 = fmul double 0x3F9C71C71C71C71C, %sub
  %add338 = fadd double 0.000000e+00, %mul161
  %add339 = fadd double 0.000000e+00, %mul161
  %mul340 = fmul double 4.500000e+00, %add339
  %add341 = fadd double %mul340, 3.000000e+00
  %mul342 = fmul double %add338, %add341
  %add343 = fadd double 1.000000e+00, %mul342
  %sub344 = fsub double %add343, %mul167
  %mul345 = fmul double %mul337, %sub344
  %add346 = add nsw i32 15, %i.0
  %idxprom347 = sext i32 %add346 to i64
  %arrayidx348 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom347
  store double %mul345, double* %arrayidx348, align 8
  %mul349 = fmul double 0x3F9C71C71C71C71C, %sub
  %sub350 = fsub double 0.000000e+00, %mul161
  %sub351 = fsub double 0.000000e+00, %mul161
  %mul352 = fmul double 4.500000e+00, %sub351
  %add353 = fadd double %mul352, 3.000000e+00
  %mul354 = fmul double %sub350, %add353
  %add355 = fadd double 1.000000e+00, %mul354
  %sub356 = fsub double %add355, %mul167
  %mul357 = fmul double %mul349, %sub356
  %add358 = add nsw i32 16, %i.0
  %idxprom359 = sext i32 %add358 to i64
  %arrayidx360 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom359
  store double %mul357, double* %arrayidx360, align 8
  %mul361 = fmul double 0x3F9C71C71C71C71C, %sub
  %fneg362 = fneg double 0.000000e+00
  %add363 = fadd double %fneg362, %mul161
  %fneg364 = fneg double 0.000000e+00
  %add365 = fadd double %fneg364, %mul161
  %mul366 = fmul double 4.500000e+00, %add365
  %add367 = fadd double %mul366, 3.000000e+00
  %mul368 = fmul double %add363, %add367
  %add369 = fadd double 1.000000e+00, %mul368
  %sub370 = fsub double %add369, %mul167
  %mul371 = fmul double %mul361, %sub370
  %add372 = add nsw i32 17, %i.0
  %idxprom373 = sext i32 %add372 to i64
  %arrayidx374 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom373
  store double %mul371, double* %arrayidx374, align 8
  %mul375 = fmul double 0x3F9C71C71C71C71C, %sub
  %fneg376 = fneg double 0.000000e+00
  %sub377 = fsub double %fneg376, %mul161
  %fneg378 = fneg double 0.000000e+00
  %sub379 = fsub double %fneg378, %mul161
  %mul380 = fmul double 4.500000e+00, %sub379
  %add381 = fadd double %mul380, 3.000000e+00
  %mul382 = fmul double %sub377, %add381
  %add383 = fadd double 1.000000e+00, %mul382
  %sub384 = fsub double %add383, %mul167
  %mul385 = fmul double %mul375, %sub384
  %add386 = add nsw i32 18, %i.0
  %idxprom387 = sext i32 %add386 to i64
  %arrayidx388 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom387
  store double %mul385, double* %arrayidx388, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %add389 = add nsw i32 %i.0, 20
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond390

for.cond390:                                      ; preds = %for.inc1018, %for.end
  %i.1 = phi i32 [ 25800000, %for.end ], [ %add1019, %for.inc1018 ]
  %cmp391 = icmp slt i32 %i.1, 26000000
  br i1 %cmp391, label %for.body393, label %for.end1020

for.body393:                                      ; preds = %for.cond390
  %add394 = add nsw i32 -200000, %i.1
  %idxprom395 = sext i32 %add394 to i64
  %arrayidx396 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom395
  %i38 = load double, double* %arrayidx396, align 8
  %add397 = add nsw i32 -199999, %i.1
  %idxprom398 = sext i32 %add397 to i64
  %arrayidx399 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom398
  %i39 = load double, double* %arrayidx399, align 8
  %add400 = fadd double %i38, %i39
  %add401 = add nsw i32 -199998, %i.1
  %idxprom402 = sext i32 %add401 to i64
  %arrayidx403 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom402
  %i40 = load double, double* %arrayidx403, align 8
  %add404 = fadd double %add400, %i40
  %add405 = add nsw i32 -199997, %i.1
  %idxprom406 = sext i32 %add405 to i64
  %arrayidx407 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom406
  %i41 = load double, double* %arrayidx407, align 8
  %add408 = fadd double %add404, %i41
  %add409 = add nsw i32 -199996, %i.1
  %idxprom410 = sext i32 %add409 to i64
  %arrayidx411 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom410
  %i42 = load double, double* %arrayidx411, align 8
  %add412 = fadd double %add408, %i42
  %add413 = add nsw i32 -199995, %i.1
  %idxprom414 = sext i32 %add413 to i64
  %arrayidx415 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom414
  %i43 = load double, double* %arrayidx415, align 8
  %add416 = fadd double %add412, %i43
  %add417 = add nsw i32 -199994, %i.1
  %idxprom418 = sext i32 %add417 to i64
  %arrayidx419 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom418
  %i44 = load double, double* %arrayidx419, align 8
  %add420 = fadd double %add416, %i44
  %add421 = add nsw i32 -199993, %i.1
  %idxprom422 = sext i32 %add421 to i64
  %arrayidx423 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom422
  %i45 = load double, double* %arrayidx423, align 8
  %add424 = fadd double %add420, %i45
  %add425 = add nsw i32 -199992, %i.1
  %idxprom426 = sext i32 %add425 to i64
  %arrayidx427 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom426
  %i46 = load double, double* %arrayidx427, align 8
  %add428 = fadd double %add424, %i46
  %add429 = add nsw i32 -199991, %i.1
  %idxprom430 = sext i32 %add429 to i64
  %arrayidx431 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom430
  %i47 = load double, double* %arrayidx431, align 8
  %add432 = fadd double %add428, %i47
  %add433 = add nsw i32 -199990, %i.1
  %idxprom434 = sext i32 %add433 to i64
  %arrayidx435 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom434
  %i48 = load double, double* %arrayidx435, align 8
  %add436 = fadd double %add432, %i48
  %add437 = add nsw i32 -199989, %i.1
  %idxprom438 = sext i32 %add437 to i64
  %arrayidx439 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom438
  %i49 = load double, double* %arrayidx439, align 8
  %add440 = fadd double %add436, %i49
  %add441 = add nsw i32 -199988, %i.1
  %idxprom442 = sext i32 %add441 to i64
  %arrayidx443 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom442
  %i50 = load double, double* %arrayidx443, align 8
  %add444 = fadd double %add440, %i50
  %add445 = add nsw i32 -199987, %i.1
  %idxprom446 = sext i32 %add445 to i64
  %arrayidx447 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom446
  %i51 = load double, double* %arrayidx447, align 8
  %add448 = fadd double %add444, %i51
  %add449 = add nsw i32 -199986, %i.1
  %idxprom450 = sext i32 %add449 to i64
  %arrayidx451 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom450
  %i52 = load double, double* %arrayidx451, align 8
  %add452 = fadd double %add448, %i52
  %add453 = add nsw i32 -199985, %i.1
  %idxprom454 = sext i32 %add453 to i64
  %arrayidx455 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom454
  %i53 = load double, double* %arrayidx455, align 8
  %add456 = fadd double %add452, %i53
  %add457 = add nsw i32 -199984, %i.1
  %idxprom458 = sext i32 %add457 to i64
  %arrayidx459 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom458
  %i54 = load double, double* %arrayidx459, align 8
  %add460 = fadd double %add456, %i54
  %add461 = add nsw i32 -199983, %i.1
  %idxprom462 = sext i32 %add461 to i64
  %arrayidx463 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom462
  %i55 = load double, double* %arrayidx463, align 8
  %add464 = fadd double %add460, %i55
  %add465 = add nsw i32 -199982, %i.1
  %idxprom466 = sext i32 %add465 to i64
  %arrayidx467 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom466
  %i56 = load double, double* %arrayidx467, align 8
  %add468 = fadd double %add464, %i56
  %add469 = add nsw i32 -199997, %i.1
  %idxprom470 = sext i32 %add469 to i64
  %arrayidx471 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom470
  %i57 = load double, double* %arrayidx471, align 8
  %add472 = add nsw i32 -199996, %i.1
  %idxprom473 = sext i32 %add472 to i64
  %arrayidx474 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom473
  %i58 = load double, double* %arrayidx474, align 8
  %sub475 = fsub double %i57, %i58
  %add476 = add nsw i32 -199993, %i.1
  %idxprom477 = sext i32 %add476 to i64
  %arrayidx478 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom477
  %i59 = load double, double* %arrayidx478, align 8
  %add479 = fadd double %sub475, %i59
  %add480 = add nsw i32 -199992, %i.1
  %idxprom481 = sext i32 %add480 to i64
  %arrayidx482 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom481
  %i60 = load double, double* %arrayidx482, align 8
  %sub483 = fsub double %add479, %i60
  %add484 = add nsw i32 -199991, %i.1
  %idxprom485 = sext i32 %add484 to i64
  %arrayidx486 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom485
  %i61 = load double, double* %arrayidx486, align 8
  %add487 = fadd double %sub483, %i61
  %add488 = add nsw i32 -199990, %i.1
  %idxprom489 = sext i32 %add488 to i64
  %arrayidx490 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom489
  %i62 = load double, double* %arrayidx490, align 8
  %sub491 = fsub double %add487, %i62
  %add492 = add nsw i32 -199985, %i.1
  %idxprom493 = sext i32 %add492 to i64
  %arrayidx494 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom493
  %i63 = load double, double* %arrayidx494, align 8
  %add495 = fadd double %sub491, %i63
  %add496 = add nsw i32 -199984, %i.1
  %idxprom497 = sext i32 %add496 to i64
  %arrayidx498 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom497
  %i64 = load double, double* %arrayidx498, align 8
  %add499 = fadd double %add495, %i64
  %add500 = add nsw i32 -199983, %i.1
  %idxprom501 = sext i32 %add500 to i64
  %arrayidx502 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom501
  %i65 = load double, double* %arrayidx502, align 8
  %sub503 = fsub double %add499, %i65
  %add504 = add nsw i32 -199982, %i.1
  %idxprom505 = sext i32 %add504 to i64
  %arrayidx506 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom505
  %i66 = load double, double* %arrayidx506, align 8
  %sub507 = fsub double %sub503, %i66
  %add508 = add nsw i32 -199999, %i.1
  %idxprom509 = sext i32 %add508 to i64
  %arrayidx510 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom509
  %i67 = load double, double* %arrayidx510, align 8
  %add511 = add nsw i32 -199998, %i.1
  %idxprom512 = sext i32 %add511 to i64
  %arrayidx513 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom512
  %i68 = load double, double* %arrayidx513, align 8
  %sub514 = fsub double %i67, %i68
  %add515 = add nsw i32 -199993, %i.1
  %idxprom516 = sext i32 %add515 to i64
  %arrayidx517 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom516
  %i69 = load double, double* %arrayidx517, align 8
  %add518 = fadd double %sub514, %i69
  %add519 = add nsw i32 -199992, %i.1
  %idxprom520 = sext i32 %add519 to i64
  %arrayidx521 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom520
  %i70 = load double, double* %arrayidx521, align 8
  %add522 = fadd double %add518, %i70
  %add523 = add nsw i32 -199991, %i.1
  %idxprom524 = sext i32 %add523 to i64
  %arrayidx525 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom524
  %i71 = load double, double* %arrayidx525, align 8
  %sub526 = fsub double %add522, %i71
  %add527 = add nsw i32 -199990, %i.1
  %idxprom528 = sext i32 %add527 to i64
  %arrayidx529 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom528
  %i72 = load double, double* %arrayidx529, align 8
  %sub530 = fsub double %sub526, %i72
  %add531 = add nsw i32 -199989, %i.1
  %idxprom532 = sext i32 %add531 to i64
  %arrayidx533 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom532
  %i73 = load double, double* %arrayidx533, align 8
  %add534 = fadd double %sub530, %i73
  %add535 = add nsw i32 -199988, %i.1
  %idxprom536 = sext i32 %add535 to i64
  %arrayidx537 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom536
  %i74 = load double, double* %arrayidx537, align 8
  %add538 = fadd double %add534, %i74
  %add539 = add nsw i32 -199987, %i.1
  %idxprom540 = sext i32 %add539 to i64
  %arrayidx541 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom540
  %i75 = load double, double* %arrayidx541, align 8
  %sub542 = fsub double %add538, %i75
  %add543 = add nsw i32 -199986, %i.1
  %idxprom544 = sext i32 %add543 to i64
  %arrayidx545 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom544
  %i76 = load double, double* %arrayidx545, align 8
  %sub546 = fsub double %sub542, %i76
  %add547 = add nsw i32 -199995, %i.1
  %idxprom548 = sext i32 %add547 to i64
  %arrayidx549 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom548
  %i77 = load double, double* %arrayidx549, align 8
  %add550 = add nsw i32 -199994, %i.1
  %idxprom551 = sext i32 %add550 to i64
  %arrayidx552 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom551
  %i78 = load double, double* %arrayidx552, align 8
  %sub553 = fsub double %i77, %i78
  %add554 = add nsw i32 -199989, %i.1
  %idxprom555 = sext i32 %add554 to i64
  %arrayidx556 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom555
  %i79 = load double, double* %arrayidx556, align 8
  %add557 = fadd double %sub553, %i79
  %add558 = add nsw i32 -199988, %i.1
  %idxprom559 = sext i32 %add558 to i64
  %arrayidx560 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom559
  %i80 = load double, double* %arrayidx560, align 8
  %sub561 = fsub double %add557, %i80
  %add562 = add nsw i32 -199987, %i.1
  %idxprom563 = sext i32 %add562 to i64
  %arrayidx564 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom563
  %i81 = load double, double* %arrayidx564, align 8
  %add565 = fadd double %sub561, %i81
  %add566 = add nsw i32 -199986, %i.1
  %idxprom567 = sext i32 %add566 to i64
  %arrayidx568 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom567
  %i82 = load double, double* %arrayidx568, align 8
  %sub569 = fsub double %add565, %i82
  %add570 = add nsw i32 -199985, %i.1
  %idxprom571 = sext i32 %add570 to i64
  %arrayidx572 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom571
  %i83 = load double, double* %arrayidx572, align 8
  %add573 = fadd double %sub569, %i83
  %add574 = add nsw i32 -199984, %i.1
  %idxprom575 = sext i32 %add574 to i64
  %arrayidx576 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom575
  %i84 = load double, double* %arrayidx576, align 8
  %sub577 = fsub double %add573, %i84
  %add578 = add nsw i32 -199983, %i.1
  %idxprom579 = sext i32 %add578 to i64
  %arrayidx580 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom579
  %i85 = load double, double* %arrayidx580, align 8
  %add581 = fadd double %sub577, %i85
  %add582 = add nsw i32 -199982, %i.1
  %idxprom583 = sext i32 %add582 to i64
  %arrayidx584 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom583
  %i86 = load double, double* %arrayidx584, align 8
  %sub585 = fsub double %add581, %i86
  %div586 = fdiv double %sub507, %add468
  %div587 = fdiv double %sub546, %add468
  %div588 = fdiv double %sub585, %add468
  %add589 = add nsw i32 -400000, %i.1
  %idxprom590 = sext i32 %add589 to i64
  %arrayidx591 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom590
  %i87 = load double, double* %arrayidx591, align 8
  %add592 = add nsw i32 -399999, %i.1
  %idxprom593 = sext i32 %add592 to i64
  %arrayidx594 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom593
  %i88 = load double, double* %arrayidx594, align 8
  %add595 = fadd double %i87, %i88
  %add596 = add nsw i32 -399998, %i.1
  %idxprom597 = sext i32 %add596 to i64
  %arrayidx598 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom597
  %i89 = load double, double* %arrayidx598, align 8
  %add599 = fadd double %add595, %i89
  %add600 = add nsw i32 -399997, %i.1
  %idxprom601 = sext i32 %add600 to i64
  %arrayidx602 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom601
  %i90 = load double, double* %arrayidx602, align 8
  %add603 = fadd double %add599, %i90
  %add604 = add nsw i32 -399996, %i.1
  %idxprom605 = sext i32 %add604 to i64
  %arrayidx606 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom605
  %i91 = load double, double* %arrayidx606, align 8
  %add607 = fadd double %add603, %i91
  %add608 = add nsw i32 -399995, %i.1
  %idxprom609 = sext i32 %add608 to i64
  %arrayidx610 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom609
  %i92 = load double, double* %arrayidx610, align 8
  %add611 = fadd double %add607, %i92
  %add612 = add nsw i32 -399994, %i.1
  %idxprom613 = sext i32 %add612 to i64
  %arrayidx614 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom613
  %i93 = load double, double* %arrayidx614, align 8
  %add615 = fadd double %add611, %i93
  %add616 = add nsw i32 -399993, %i.1
  %idxprom617 = sext i32 %add616 to i64
  %arrayidx618 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom617
  %i94 = load double, double* %arrayidx618, align 8
  %add619 = fadd double %add615, %i94
  %add620 = add nsw i32 -399992, %i.1
  %idxprom621 = sext i32 %add620 to i64
  %arrayidx622 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom621
  %i95 = load double, double* %arrayidx622, align 8
  %add623 = fadd double %add619, %i95
  %add624 = add nsw i32 -399991, %i.1
  %idxprom625 = sext i32 %add624 to i64
  %arrayidx626 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom625
  %i96 = load double, double* %arrayidx626, align 8
  %add627 = fadd double %add623, %i96
  %add628 = add nsw i32 -399990, %i.1
  %idxprom629 = sext i32 %add628 to i64
  %arrayidx630 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom629
  %i97 = load double, double* %arrayidx630, align 8
  %add631 = fadd double %add627, %i97
  %add632 = add nsw i32 -399989, %i.1
  %idxprom633 = sext i32 %add632 to i64
  %arrayidx634 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom633
  %i98 = load double, double* %arrayidx634, align 8
  %add635 = fadd double %add631, %i98
  %add636 = add nsw i32 -399988, %i.1
  %idxprom637 = sext i32 %add636 to i64
  %arrayidx638 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom637
  %i99 = load double, double* %arrayidx638, align 8
  %add639 = fadd double %add635, %i99
  %add640 = add nsw i32 -399987, %i.1
  %idxprom641 = sext i32 %add640 to i64
  %arrayidx642 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom641
  %i100 = load double, double* %arrayidx642, align 8
  %add643 = fadd double %add639, %i100
  %add644 = add nsw i32 -399986, %i.1
  %idxprom645 = sext i32 %add644 to i64
  %arrayidx646 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom645
  %i101 = load double, double* %arrayidx646, align 8
  %add647 = fadd double %add643, %i101
  %add648 = add nsw i32 -399985, %i.1
  %idxprom649 = sext i32 %add648 to i64
  %arrayidx650 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom649
  %i102 = load double, double* %arrayidx650, align 8
  %add651 = fadd double %add647, %i102
  %add652 = add nsw i32 -399984, %i.1
  %idxprom653 = sext i32 %add652 to i64
  %arrayidx654 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom653
  %i103 = load double, double* %arrayidx654, align 8
  %add655 = fadd double %add651, %i103
  %add656 = add nsw i32 -399983, %i.1
  %idxprom657 = sext i32 %add656 to i64
  %arrayidx658 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom657
  %i104 = load double, double* %arrayidx658, align 8
  %add659 = fadd double %add655, %i104
  %add660 = add nsw i32 -399982, %i.1
  %idxprom661 = sext i32 %add660 to i64
  %arrayidx662 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom661
  %i105 = load double, double* %arrayidx662, align 8
  %add663 = fadd double %add659, %i105
  %add664 = add nsw i32 -399997, %i.1
  %idxprom665 = sext i32 %add664 to i64
  %arrayidx666 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom665
  %i106 = load double, double* %arrayidx666, align 8
  %add667 = add nsw i32 -399996, %i.1
  %idxprom668 = sext i32 %add667 to i64
  %arrayidx669 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom668
  %i107 = load double, double* %arrayidx669, align 8
  %sub670 = fsub double %i106, %i107
  %add671 = add nsw i32 -399993, %i.1
  %idxprom672 = sext i32 %add671 to i64
  %arrayidx673 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom672
  %i108 = load double, double* %arrayidx673, align 8
  %add674 = fadd double %sub670, %i108
  %add675 = add nsw i32 -399992, %i.1
  %idxprom676 = sext i32 %add675 to i64
  %arrayidx677 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom676
  %i109 = load double, double* %arrayidx677, align 8
  %sub678 = fsub double %add674, %i109
  %add679 = add nsw i32 -399991, %i.1
  %idxprom680 = sext i32 %add679 to i64
  %arrayidx681 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom680
  %i110 = load double, double* %arrayidx681, align 8
  %add682 = fadd double %sub678, %i110
  %add683 = add nsw i32 -399990, %i.1
  %idxprom684 = sext i32 %add683 to i64
  %arrayidx685 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom684
  %i111 = load double, double* %arrayidx685, align 8
  %sub686 = fsub double %add682, %i111
  %add687 = add nsw i32 -399985, %i.1
  %idxprom688 = sext i32 %add687 to i64
  %arrayidx689 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom688
  %i112 = load double, double* %arrayidx689, align 8
  %add690 = fadd double %sub686, %i112
  %add691 = add nsw i32 -399984, %i.1
  %idxprom692 = sext i32 %add691 to i64
  %arrayidx693 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom692
  %i113 = load double, double* %arrayidx693, align 8
  %add694 = fadd double %add690, %i113
  %add695 = add nsw i32 -399983, %i.1
  %idxprom696 = sext i32 %add695 to i64
  %arrayidx697 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom696
  %i114 = load double, double* %arrayidx697, align 8
  %sub698 = fsub double %add694, %i114
  %add699 = add nsw i32 -399982, %i.1
  %idxprom700 = sext i32 %add699 to i64
  %arrayidx701 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom700
  %i115 = load double, double* %arrayidx701, align 8
  %sub702 = fsub double %sub698, %i115
  %add703 = add nsw i32 -399999, %i.1
  %idxprom704 = sext i32 %add703 to i64
  %arrayidx705 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom704
  %i116 = load double, double* %arrayidx705, align 8
  %add706 = add nsw i32 -399998, %i.1
  %idxprom707 = sext i32 %add706 to i64
  %arrayidx708 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom707
  %i117 = load double, double* %arrayidx708, align 8
  %sub709 = fsub double %i116, %i117
  %add710 = add nsw i32 -399993, %i.1
  %idxprom711 = sext i32 %add710 to i64
  %arrayidx712 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom711
  %i118 = load double, double* %arrayidx712, align 8
  %add713 = fadd double %sub709, %i118
  %add714 = add nsw i32 -399992, %i.1
  %idxprom715 = sext i32 %add714 to i64
  %arrayidx716 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom715
  %i119 = load double, double* %arrayidx716, align 8
  %add717 = fadd double %add713, %i119
  %add718 = add nsw i32 -399991, %i.1
  %idxprom719 = sext i32 %add718 to i64
  %arrayidx720 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom719
  %i120 = load double, double* %arrayidx720, align 8
  %sub721 = fsub double %add717, %i120
  %add722 = add nsw i32 -399990, %i.1
  %idxprom723 = sext i32 %add722 to i64
  %arrayidx724 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom723
  %i121 = load double, double* %arrayidx724, align 8
  %sub725 = fsub double %sub721, %i121
  %add726 = add nsw i32 -399989, %i.1
  %idxprom727 = sext i32 %add726 to i64
  %arrayidx728 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom727
  %i122 = load double, double* %arrayidx728, align 8
  %add729 = fadd double %sub725, %i122
  %add730 = add nsw i32 -399988, %i.1
  %idxprom731 = sext i32 %add730 to i64
  %arrayidx732 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom731
  %i123 = load double, double* %arrayidx732, align 8
  %add733 = fadd double %add729, %i123
  %add734 = add nsw i32 -399987, %i.1
  %idxprom735 = sext i32 %add734 to i64
  %arrayidx736 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom735
  %i124 = load double, double* %arrayidx736, align 8
  %sub737 = fsub double %add733, %i124
  %add738 = add nsw i32 -399986, %i.1
  %idxprom739 = sext i32 %add738 to i64
  %arrayidx740 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom739
  %i125 = load double, double* %arrayidx740, align 8
  %sub741 = fsub double %sub737, %i125
  %add742 = add nsw i32 -399995, %i.1
  %idxprom743 = sext i32 %add742 to i64
  %arrayidx744 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom743
  %i126 = load double, double* %arrayidx744, align 8
  %add745 = add nsw i32 -399994, %i.1
  %idxprom746 = sext i32 %add745 to i64
  %arrayidx747 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom746
  %i127 = load double, double* %arrayidx747, align 8
  %sub748 = fsub double %i126, %i127
  %add749 = add nsw i32 -399989, %i.1
  %idxprom750 = sext i32 %add749 to i64
  %arrayidx751 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom750
  %i128 = load double, double* %arrayidx751, align 8
  %add752 = fadd double %sub748, %i128
  %add753 = add nsw i32 -399988, %i.1
  %idxprom754 = sext i32 %add753 to i64
  %arrayidx755 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom754
  %i129 = load double, double* %arrayidx755, align 8
  %sub756 = fsub double %add752, %i129
  %add757 = add nsw i32 -399987, %i.1
  %idxprom758 = sext i32 %add757 to i64
  %arrayidx759 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom758
  %i130 = load double, double* %arrayidx759, align 8
  %add760 = fadd double %sub756, %i130
  %add761 = add nsw i32 -399986, %i.1
  %idxprom762 = sext i32 %add761 to i64
  %arrayidx763 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom762
  %i131 = load double, double* %arrayidx763, align 8
  %sub764 = fsub double %add760, %i131
  %add765 = add nsw i32 -399985, %i.1
  %idxprom766 = sext i32 %add765 to i64
  %arrayidx767 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom766
  %i132 = load double, double* %arrayidx767, align 8
  %add768 = fadd double %sub764, %i132
  %add769 = add nsw i32 -399984, %i.1
  %idxprom770 = sext i32 %add769 to i64
  %arrayidx771 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom770
  %i133 = load double, double* %arrayidx771, align 8
  %sub772 = fsub double %add768, %i133
  %add773 = add nsw i32 -399983, %i.1
  %idxprom774 = sext i32 %add773 to i64
  %arrayidx775 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom774
  %i134 = load double, double* %arrayidx775, align 8
  %add776 = fadd double %sub772, %i134
  %add777 = add nsw i32 -399982, %i.1
  %idxprom778 = sext i32 %add777 to i64
  %arrayidx779 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom778
  %i135 = load double, double* %arrayidx779, align 8
  %sub780 = fsub double %add776, %i135
  %div781 = fdiv double %sub702, %add663
  %div782 = fdiv double %sub741, %add663
  %div783 = fdiv double %sub780, %add663
  %mul784 = fmul double 2.000000e+00, %div586
  %sub785 = fsub double %mul784, %div781
  %mul786 = fmul double 2.000000e+00, %div587
  %sub787 = fsub double %mul786, %div782
  %mul788 = fmul double 2.000000e+00, %div588
  %sub789 = fsub double %mul788, %div783
  %mul790 = fmul double %sub785, %sub785
  %mul791 = fmul double %sub787, %sub787
  %add792 = fadd double %mul790, %mul791
  %mul793 = fmul double %sub789, %sub789
  %add794 = fadd double %add792, %mul793
  %mul795 = fmul double 1.500000e+00, %add794
  %mul796 = fmul double 0x3FD5555555555555, 1.000000e+00
  %sub797 = fsub double 1.000000e+00, %mul795
  %mul798 = fmul double %mul796, %sub797
  %add799 = add nsw i32 0, %i.1
  %idxprom800 = sext i32 %add799 to i64
  %arrayidx801 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom800
  store double %mul798, double* %arrayidx801, align 8
  %mul802 = fmul double 0x3FAC71C71C71C71C, 1.000000e+00
  %mul803 = fmul double 4.500000e+00, %sub787
  %add804 = fadd double %mul803, 3.000000e+00
  %mul805 = fmul double %sub787, %add804
  %add806 = fadd double 1.000000e+00, %mul805
  %sub807 = fsub double %add806, %mul795
  %mul808 = fmul double %mul802, %sub807
  %add809 = add nsw i32 1, %i.1
  %idxprom810 = sext i32 %add809 to i64
  %arrayidx811 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom810
  store double %mul808, double* %arrayidx811, align 8
  %mul812 = fmul double 0x3FAC71C71C71C71C, 1.000000e+00
  %mul813 = fmul double 4.500000e+00, %sub787
  %sub814 = fsub double %mul813, 3.000000e+00
  %mul815 = fmul double %sub787, %sub814
  %add816 = fadd double 1.000000e+00, %mul815
  %sub817 = fsub double %add816, %mul795
  %mul818 = fmul double %mul812, %sub817
  %add819 = add nsw i32 2, %i.1
  %idxprom820 = sext i32 %add819 to i64
  %arrayidx821 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom820
  store double %mul818, double* %arrayidx821, align 8
  %mul822 = fmul double 0x3FAC71C71C71C71C, 1.000000e+00
  %mul823 = fmul double 4.500000e+00, %sub785
  %add824 = fadd double %mul823, 3.000000e+00
  %mul825 = fmul double %sub785, %add824
  %add826 = fadd double 1.000000e+00, %mul825
  %sub827 = fsub double %add826, %mul795
  %mul828 = fmul double %mul822, %sub827
  %add829 = add nsw i32 3, %i.1
  %idxprom830 = sext i32 %add829 to i64
  %arrayidx831 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom830
  store double %mul828, double* %arrayidx831, align 8
  %mul832 = fmul double 0x3FAC71C71C71C71C, 1.000000e+00
  %mul833 = fmul double 4.500000e+00, %sub785
  %sub834 = fsub double %mul833, 3.000000e+00
  %mul835 = fmul double %sub785, %sub834
  %add836 = fadd double 1.000000e+00, %mul835
  %sub837 = fsub double %add836, %mul795
  %mul838 = fmul double %mul832, %sub837
  %add839 = add nsw i32 4, %i.1
  %idxprom840 = sext i32 %add839 to i64
  %arrayidx841 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom840
  store double %mul838, double* %arrayidx841, align 8
  %mul842 = fmul double 0x3FAC71C71C71C71C, 1.000000e+00
  %mul843 = fmul double 4.500000e+00, %sub789
  %add844 = fadd double %mul843, 3.000000e+00
  %mul845 = fmul double %sub789, %add844
  %add846 = fadd double 1.000000e+00, %mul845
  %sub847 = fsub double %add846, %mul795
  %mul848 = fmul double %mul842, %sub847
  %add849 = add nsw i32 5, %i.1
  %idxprom850 = sext i32 %add849 to i64
  %arrayidx851 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom850
  store double %mul848, double* %arrayidx851, align 8
  %mul852 = fmul double 0x3FAC71C71C71C71C, 1.000000e+00
  %mul853 = fmul double 4.500000e+00, %sub789
  %sub854 = fsub double %mul853, 3.000000e+00
  %mul855 = fmul double %sub789, %sub854
  %add856 = fadd double 1.000000e+00, %mul855
  %sub857 = fsub double %add856, %mul795
  %mul858 = fmul double %mul852, %sub857
  %add859 = add nsw i32 6, %i.1
  %idxprom860 = sext i32 %add859 to i64
  %arrayidx861 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom860
  store double %mul858, double* %arrayidx861, align 8
  %mul862 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %add863 = fadd double %sub785, %sub787
  %add864 = fadd double %sub785, %sub787
  %mul865 = fmul double 4.500000e+00, %add864
  %add866 = fadd double %mul865, 3.000000e+00
  %mul867 = fmul double %add863, %add866
  %add868 = fadd double 1.000000e+00, %mul867
  %sub869 = fsub double %add868, %mul795
  %mul870 = fmul double %mul862, %sub869
  %add871 = add nsw i32 7, %i.1
  %idxprom872 = sext i32 %add871 to i64
  %arrayidx873 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom872
  store double %mul870, double* %arrayidx873, align 8
  %mul874 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %fneg875 = fneg double %sub785
  %add876 = fadd double %fneg875, %sub787
  %fneg877 = fneg double %sub785
  %add878 = fadd double %fneg877, %sub787
  %mul879 = fmul double 4.500000e+00, %add878
  %add880 = fadd double %mul879, 3.000000e+00
  %mul881 = fmul double %add876, %add880
  %add882 = fadd double 1.000000e+00, %mul881
  %sub883 = fsub double %add882, %mul795
  %mul884 = fmul double %mul874, %sub883
  %add885 = add nsw i32 8, %i.1
  %idxprom886 = sext i32 %add885 to i64
  %arrayidx887 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom886
  store double %mul884, double* %arrayidx887, align 8
  %mul888 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %sub889 = fsub double %sub785, %sub787
  %sub890 = fsub double %sub785, %sub787
  %mul891 = fmul double 4.500000e+00, %sub890
  %add892 = fadd double %mul891, 3.000000e+00
  %mul893 = fmul double %sub889, %add892
  %add894 = fadd double 1.000000e+00, %mul893
  %sub895 = fsub double %add894, %mul795
  %mul896 = fmul double %mul888, %sub895
  %add897 = add nsw i32 9, %i.1
  %idxprom898 = sext i32 %add897 to i64
  %arrayidx899 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom898
  store double %mul896, double* %arrayidx899, align 8
  %mul900 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %fneg901 = fneg double %sub785
  %sub902 = fsub double %fneg901, %sub787
  %fneg903 = fneg double %sub785
  %sub904 = fsub double %fneg903, %sub787
  %mul905 = fmul double 4.500000e+00, %sub904
  %add906 = fadd double %mul905, 3.000000e+00
  %mul907 = fmul double %sub902, %add906
  %add908 = fadd double 1.000000e+00, %mul907
  %sub909 = fsub double %add908, %mul795
  %mul910 = fmul double %mul900, %sub909
  %add911 = add nsw i32 10, %i.1
  %idxprom912 = sext i32 %add911 to i64
  %arrayidx913 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom912
  store double %mul910, double* %arrayidx913, align 8
  %mul914 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %add915 = fadd double %sub787, %sub789
  %add916 = fadd double %sub787, %sub789
  %mul917 = fmul double 4.500000e+00, %add916
  %add918 = fadd double %mul917, 3.000000e+00
  %mul919 = fmul double %add915, %add918
  %add920 = fadd double 1.000000e+00, %mul919
  %sub921 = fsub double %add920, %mul795
  %mul922 = fmul double %mul914, %sub921
  %add923 = add nsw i32 11, %i.1
  %idxprom924 = sext i32 %add923 to i64
  %arrayidx925 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom924
  store double %mul922, double* %arrayidx925, align 8
  %mul926 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %sub927 = fsub double %sub787, %sub789
  %sub928 = fsub double %sub787, %sub789
  %mul929 = fmul double 4.500000e+00, %sub928
  %add930 = fadd double %mul929, 3.000000e+00
  %mul931 = fmul double %sub927, %add930
  %add932 = fadd double 1.000000e+00, %mul931
  %sub933 = fsub double %add932, %mul795
  %mul934 = fmul double %mul926, %sub933
  %add935 = add nsw i32 12, %i.1
  %idxprom936 = sext i32 %add935 to i64
  %arrayidx937 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom936
  store double %mul934, double* %arrayidx937, align 8
  %mul938 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %fneg939 = fneg double %sub787
  %add940 = fadd double %fneg939, %sub789
  %fneg941 = fneg double %sub787
  %add942 = fadd double %fneg941, %sub789
  %mul943 = fmul double 4.500000e+00, %add942
  %add944 = fadd double %mul943, 3.000000e+00
  %mul945 = fmul double %add940, %add944
  %add946 = fadd double 1.000000e+00, %mul945
  %sub947 = fsub double %add946, %mul795
  %mul948 = fmul double %mul938, %sub947
  %add949 = add nsw i32 13, %i.1
  %idxprom950 = sext i32 %add949 to i64
  %arrayidx951 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom950
  store double %mul948, double* %arrayidx951, align 8
  %mul952 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %fneg953 = fneg double %sub787
  %sub954 = fsub double %fneg953, %sub789
  %fneg955 = fneg double %sub787
  %sub956 = fsub double %fneg955, %sub789
  %mul957 = fmul double 4.500000e+00, %sub956
  %add958 = fadd double %mul957, 3.000000e+00
  %mul959 = fmul double %sub954, %add958
  %add960 = fadd double 1.000000e+00, %mul959
  %sub961 = fsub double %add960, %mul795
  %mul962 = fmul double %mul952, %sub961
  %add963 = add nsw i32 14, %i.1
  %idxprom964 = sext i32 %add963 to i64
  %arrayidx965 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom964
  store double %mul962, double* %arrayidx965, align 8
  %mul966 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %add967 = fadd double %sub785, %sub789
  %add968 = fadd double %sub785, %sub789
  %mul969 = fmul double 4.500000e+00, %add968
  %add970 = fadd double %mul969, 3.000000e+00
  %mul971 = fmul double %add967, %add970
  %add972 = fadd double 1.000000e+00, %mul971
  %sub973 = fsub double %add972, %mul795
  %mul974 = fmul double %mul966, %sub973
  %add975 = add nsw i32 15, %i.1
  %idxprom976 = sext i32 %add975 to i64
  %arrayidx977 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom976
  store double %mul974, double* %arrayidx977, align 8
  %mul978 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %sub979 = fsub double %sub785, %sub789
  %sub980 = fsub double %sub785, %sub789
  %mul981 = fmul double 4.500000e+00, %sub980
  %add982 = fadd double %mul981, 3.000000e+00
  %mul983 = fmul double %sub979, %add982
  %add984 = fadd double 1.000000e+00, %mul983
  %sub985 = fsub double %add984, %mul795
  %mul986 = fmul double %mul978, %sub985
  %add987 = add nsw i32 16, %i.1
  %idxprom988 = sext i32 %add987 to i64
  %arrayidx989 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom988
  store double %mul986, double* %arrayidx989, align 8
  %mul990 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %fneg991 = fneg double %sub785
  %add992 = fadd double %fneg991, %sub789
  %fneg993 = fneg double %sub785
  %add994 = fadd double %fneg993, %sub789
  %mul995 = fmul double 4.500000e+00, %add994
  %add996 = fadd double %mul995, 3.000000e+00
  %mul997 = fmul double %add992, %add996
  %add998 = fadd double 1.000000e+00, %mul997
  %sub999 = fsub double %add998, %mul795
  %mul1000 = fmul double %mul990, %sub999
  %add1001 = add nsw i32 17, %i.1
  %idxprom1002 = sext i32 %add1001 to i64
  %arrayidx1003 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom1002
  store double %mul1000, double* %arrayidx1003, align 8
  %mul1004 = fmul double 0x3F9C71C71C71C71C, 1.000000e+00
  %fneg1005 = fneg double %sub785
  %sub1006 = fsub double %fneg1005, %sub789
  %fneg1007 = fneg double %sub785
  %sub1008 = fsub double %fneg1007, %sub789
  %mul1009 = fmul double 4.500000e+00, %sub1008
  %add1010 = fadd double %mul1009, 3.000000e+00
  %mul1011 = fmul double %sub1006, %add1010
  %add1012 = fadd double 1.000000e+00, %mul1011
  %sub1013 = fsub double %add1012, %mul795
  %mul1014 = fmul double %mul1004, %sub1013
  %add1015 = add nsw i32 18, %i.1
  %idxprom1016 = sext i32 %add1015 to i64
  %arrayidx1017 = getelementptr inbounds double, double* %srcGrid, i64 %idxprom1016
  store double %mul1014, double* %arrayidx1017, align 8
  br label %for.inc1018

for.inc1018:                                      ; preds = %for.body393
  %add1019 = add nsw i32 %i.1, 20
  br label %for.cond390

for.end1020:                                      ; preds = %for.cond390
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_showGridStatistics(double* %grid) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %maxU2.0 = phi double [ -1.000000e+30, %entry ], [ %maxU2.2, %for.inc ]
  %minU2.0 = phi double [ 1.000000e+30, %entry ], [ %minU2.2, %for.inc ]
  %minRho.0 = phi double [ 1.000000e+30, %entry ], [ %minRho.1, %for.inc ]
  %maxRho.0 = phi double [ -1.000000e+30, %entry ], [ %maxRho.1, %for.inc ]
  %mass.0 = phi double [ 0.000000e+00, %entry ], [ %add77, %for.inc ]
  %nFluidCells.0 = phi i32 [ 0, %entry ], [ %nFluidCells.2, %for.inc ]
  %nAccelCells.0 = phi i32 [ 0, %entry ], [ %nAccelCells.2, %for.inc ]
  %nObstacleCells.0 = phi i32 [ 0, %entry ], [ %nObstacleCells.1, %for.inc ]
  %i.0 = phi i32 [ 0, %entry ], [ %add220, %for.inc ]
  %cmp = icmp slt i32 %i.0, 26000000
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %add = add nsw i32 0, %i.0
  %idxprom = sext i32 %add to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  %i = load double, double* %arrayidx, align 8
  %add1 = add nsw i32 1, %i.0
  %idxprom2 = sext i32 %add1 to i64
  %arrayidx3 = getelementptr inbounds double, double* %grid, i64 %idxprom2
  %i1 = load double, double* %arrayidx3, align 8
  %add4 = fadd double %i, %i1
  %add5 = add nsw i32 2, %i.0
  %idxprom6 = sext i32 %add5 to i64
  %arrayidx7 = getelementptr inbounds double, double* %grid, i64 %idxprom6
  %i2 = load double, double* %arrayidx7, align 8
  %add8 = fadd double %add4, %i2
  %add9 = add nsw i32 3, %i.0
  %idxprom10 = sext i32 %add9 to i64
  %arrayidx11 = getelementptr inbounds double, double* %grid, i64 %idxprom10
  %i3 = load double, double* %arrayidx11, align 8
  %add12 = fadd double %add8, %i3
  %add13 = add nsw i32 4, %i.0
  %idxprom14 = sext i32 %add13 to i64
  %arrayidx15 = getelementptr inbounds double, double* %grid, i64 %idxprom14
  %i4 = load double, double* %arrayidx15, align 8
  %add16 = fadd double %add12, %i4
  %add17 = add nsw i32 5, %i.0
  %idxprom18 = sext i32 %add17 to i64
  %arrayidx19 = getelementptr inbounds double, double* %grid, i64 %idxprom18
  %i5 = load double, double* %arrayidx19, align 8
  %add20 = fadd double %add16, %i5
  %add21 = add nsw i32 6, %i.0
  %idxprom22 = sext i32 %add21 to i64
  %arrayidx23 = getelementptr inbounds double, double* %grid, i64 %idxprom22
  %i6 = load double, double* %arrayidx23, align 8
  %add24 = fadd double %add20, %i6
  %add25 = add nsw i32 7, %i.0
  %idxprom26 = sext i32 %add25 to i64
  %arrayidx27 = getelementptr inbounds double, double* %grid, i64 %idxprom26
  %i7 = load double, double* %arrayidx27, align 8
  %add28 = fadd double %add24, %i7
  %add29 = add nsw i32 8, %i.0
  %idxprom30 = sext i32 %add29 to i64
  %arrayidx31 = getelementptr inbounds double, double* %grid, i64 %idxprom30
  %i8 = load double, double* %arrayidx31, align 8
  %add32 = fadd double %add28, %i8
  %add33 = add nsw i32 9, %i.0
  %idxprom34 = sext i32 %add33 to i64
  %arrayidx35 = getelementptr inbounds double, double* %grid, i64 %idxprom34
  %i9 = load double, double* %arrayidx35, align 8
  %add36 = fadd double %add32, %i9
  %add37 = add nsw i32 10, %i.0
  %idxprom38 = sext i32 %add37 to i64
  %arrayidx39 = getelementptr inbounds double, double* %grid, i64 %idxprom38
  %i10 = load double, double* %arrayidx39, align 8
  %add40 = fadd double %add36, %i10
  %add41 = add nsw i32 11, %i.0
  %idxprom42 = sext i32 %add41 to i64
  %arrayidx43 = getelementptr inbounds double, double* %grid, i64 %idxprom42
  %i11 = load double, double* %arrayidx43, align 8
  %add44 = fadd double %add40, %i11
  %add45 = add nsw i32 12, %i.0
  %idxprom46 = sext i32 %add45 to i64
  %arrayidx47 = getelementptr inbounds double, double* %grid, i64 %idxprom46
  %i12 = load double, double* %arrayidx47, align 8
  %add48 = fadd double %add44, %i12
  %add49 = add nsw i32 13, %i.0
  %idxprom50 = sext i32 %add49 to i64
  %arrayidx51 = getelementptr inbounds double, double* %grid, i64 %idxprom50
  %i13 = load double, double* %arrayidx51, align 8
  %add52 = fadd double %add48, %i13
  %add53 = add nsw i32 14, %i.0
  %idxprom54 = sext i32 %add53 to i64
  %arrayidx55 = getelementptr inbounds double, double* %grid, i64 %idxprom54
  %i14 = load double, double* %arrayidx55, align 8
  %add56 = fadd double %add52, %i14
  %add57 = add nsw i32 15, %i.0
  %idxprom58 = sext i32 %add57 to i64
  %arrayidx59 = getelementptr inbounds double, double* %grid, i64 %idxprom58
  %i15 = load double, double* %arrayidx59, align 8
  %add60 = fadd double %add56, %i15
  %add61 = add nsw i32 16, %i.0
  %idxprom62 = sext i32 %add61 to i64
  %arrayidx63 = getelementptr inbounds double, double* %grid, i64 %idxprom62
  %i16 = load double, double* %arrayidx63, align 8
  %add64 = fadd double %add60, %i16
  %add65 = add nsw i32 17, %i.0
  %idxprom66 = sext i32 %add65 to i64
  %arrayidx67 = getelementptr inbounds double, double* %grid, i64 %idxprom66
  %i17 = load double, double* %arrayidx67, align 8
  %add68 = fadd double %add64, %i17
  %add69 = add nsw i32 18, %i.0
  %idxprom70 = sext i32 %add69 to i64
  %arrayidx71 = getelementptr inbounds double, double* %grid, i64 %idxprom70
  %i18 = load double, double* %arrayidx71, align 8
  %add72 = fadd double %add68, %i18
  %cmp73 = fcmp olt double %add72, %minRho.0
  br i1 %cmp73, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %minRho.1 = phi double [ %add72, %if.then ], [ %minRho.0, %for.body ]
  %cmp74 = fcmp ogt double %add72, %maxRho.0
  br i1 %cmp74, label %if.then75, label %if.end76

if.then75:                                        ; preds = %if.end
  br label %if.end76

if.end76:                                         ; preds = %if.then75, %if.end
  %maxRho.1 = phi double [ %add72, %if.then75 ], [ %maxRho.0, %if.end ]
  %add77 = fadd double %mass.0, %add72
  %add78 = add nsw i32 19, %i.0
  %idxprom79 = sext i32 %add78 to i64
  %arrayidx80 = getelementptr inbounds double, double* %grid, i64 %idxprom79
  %i19 = bitcast double* %arrayidx80 to i8*
  %i20 = bitcast i8* %i19 to i32*
  %i21 = load i32, i32* %i20, align 4
  %and = and i32 %i21, 1
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.then81, label %if.else

if.then81:                                        ; preds = %if.end76
  %inc = add nsw i32 %nObstacleCells.0, 1
  br label %if.end219

if.else:                                          ; preds = %if.end76
  %add82 = add nsw i32 19, %i.0
  %idxprom83 = sext i32 %add82 to i64
  %arrayidx84 = getelementptr inbounds double, double* %grid, i64 %idxprom83
  %i22 = bitcast double* %arrayidx84 to i8*
  %i23 = bitcast i8* %i22 to i32*
  %i24 = load i32, i32* %i23, align 4
  %and85 = and i32 %i24, 2
  %tobool86 = icmp ne i32 %and85, 0
  br i1 %tobool86, label %if.then87, label %if.else89

if.then87:                                        ; preds = %if.else
  %inc88 = add nsw i32 %nAccelCells.0, 1
  br label %if.end91

if.else89:                                        ; preds = %if.else
  %inc90 = add nsw i32 %nFluidCells.0, 1
  br label %if.end91

if.end91:                                         ; preds = %if.else89, %if.then87
  %nFluidCells.1 = phi i32 [ %nFluidCells.0, %if.then87 ], [ %inc90, %if.else89 ]
  %nAccelCells.1 = phi i32 [ %inc88, %if.then87 ], [ %nAccelCells.0, %if.else89 ]
  %add92 = add nsw i32 3, %i.0
  %idxprom93 = sext i32 %add92 to i64
  %arrayidx94 = getelementptr inbounds double, double* %grid, i64 %idxprom93
  %i25 = load double, double* %arrayidx94, align 8
  %add95 = add nsw i32 4, %i.0
  %idxprom96 = sext i32 %add95 to i64
  %arrayidx97 = getelementptr inbounds double, double* %grid, i64 %idxprom96
  %i26 = load double, double* %arrayidx97, align 8
  %sub = fsub double %i25, %i26
  %add98 = add nsw i32 7, %i.0
  %idxprom99 = sext i32 %add98 to i64
  %arrayidx100 = getelementptr inbounds double, double* %grid, i64 %idxprom99
  %i27 = load double, double* %arrayidx100, align 8
  %add101 = fadd double %sub, %i27
  %add102 = add nsw i32 8, %i.0
  %idxprom103 = sext i32 %add102 to i64
  %arrayidx104 = getelementptr inbounds double, double* %grid, i64 %idxprom103
  %i28 = load double, double* %arrayidx104, align 8
  %sub105 = fsub double %add101, %i28
  %add106 = add nsw i32 9, %i.0
  %idxprom107 = sext i32 %add106 to i64
  %arrayidx108 = getelementptr inbounds double, double* %grid, i64 %idxprom107
  %i29 = load double, double* %arrayidx108, align 8
  %add109 = fadd double %sub105, %i29
  %add110 = add nsw i32 10, %i.0
  %idxprom111 = sext i32 %add110 to i64
  %arrayidx112 = getelementptr inbounds double, double* %grid, i64 %idxprom111
  %i30 = load double, double* %arrayidx112, align 8
  %sub113 = fsub double %add109, %i30
  %add114 = add nsw i32 15, %i.0
  %idxprom115 = sext i32 %add114 to i64
  %arrayidx116 = getelementptr inbounds double, double* %grid, i64 %idxprom115
  %i31 = load double, double* %arrayidx116, align 8
  %add117 = fadd double %sub113, %i31
  %add118 = add nsw i32 16, %i.0
  %idxprom119 = sext i32 %add118 to i64
  %arrayidx120 = getelementptr inbounds double, double* %grid, i64 %idxprom119
  %i32 = load double, double* %arrayidx120, align 8
  %add121 = fadd double %add117, %i32
  %add122 = add nsw i32 17, %i.0
  %idxprom123 = sext i32 %add122 to i64
  %arrayidx124 = getelementptr inbounds double, double* %grid, i64 %idxprom123
  %i33 = load double, double* %arrayidx124, align 8
  %sub125 = fsub double %add121, %i33
  %add126 = add nsw i32 18, %i.0
  %idxprom127 = sext i32 %add126 to i64
  %arrayidx128 = getelementptr inbounds double, double* %grid, i64 %idxprom127
  %i34 = load double, double* %arrayidx128, align 8
  %sub129 = fsub double %sub125, %i34
  %add130 = add nsw i32 1, %i.0
  %idxprom131 = sext i32 %add130 to i64
  %arrayidx132 = getelementptr inbounds double, double* %grid, i64 %idxprom131
  %i35 = load double, double* %arrayidx132, align 8
  %add133 = add nsw i32 2, %i.0
  %idxprom134 = sext i32 %add133 to i64
  %arrayidx135 = getelementptr inbounds double, double* %grid, i64 %idxprom134
  %i36 = load double, double* %arrayidx135, align 8
  %sub136 = fsub double %i35, %i36
  %add137 = add nsw i32 7, %i.0
  %idxprom138 = sext i32 %add137 to i64
  %arrayidx139 = getelementptr inbounds double, double* %grid, i64 %idxprom138
  %i37 = load double, double* %arrayidx139, align 8
  %add140 = fadd double %sub136, %i37
  %add141 = add nsw i32 8, %i.0
  %idxprom142 = sext i32 %add141 to i64
  %arrayidx143 = getelementptr inbounds double, double* %grid, i64 %idxprom142
  %i38 = load double, double* %arrayidx143, align 8
  %add144 = fadd double %add140, %i38
  %add145 = add nsw i32 9, %i.0
  %idxprom146 = sext i32 %add145 to i64
  %arrayidx147 = getelementptr inbounds double, double* %grid, i64 %idxprom146
  %i39 = load double, double* %arrayidx147, align 8
  %sub148 = fsub double %add144, %i39
  %add149 = add nsw i32 10, %i.0
  %idxprom150 = sext i32 %add149 to i64
  %arrayidx151 = getelementptr inbounds double, double* %grid, i64 %idxprom150
  %i40 = load double, double* %arrayidx151, align 8
  %sub152 = fsub double %sub148, %i40
  %add153 = add nsw i32 11, %i.0
  %idxprom154 = sext i32 %add153 to i64
  %arrayidx155 = getelementptr inbounds double, double* %grid, i64 %idxprom154
  %i41 = load double, double* %arrayidx155, align 8
  %add156 = fadd double %sub152, %i41
  %add157 = add nsw i32 12, %i.0
  %idxprom158 = sext i32 %add157 to i64
  %arrayidx159 = getelementptr inbounds double, double* %grid, i64 %idxprom158
  %i42 = load double, double* %arrayidx159, align 8
  %add160 = fadd double %add156, %i42
  %add161 = add nsw i32 13, %i.0
  %idxprom162 = sext i32 %add161 to i64
  %arrayidx163 = getelementptr inbounds double, double* %grid, i64 %idxprom162
  %i43 = load double, double* %arrayidx163, align 8
  %sub164 = fsub double %add160, %i43
  %add165 = add nsw i32 14, %i.0
  %idxprom166 = sext i32 %add165 to i64
  %arrayidx167 = getelementptr inbounds double, double* %grid, i64 %idxprom166
  %i44 = load double, double* %arrayidx167, align 8
  %sub168 = fsub double %sub164, %i44
  %add169 = add nsw i32 5, %i.0
  %idxprom170 = sext i32 %add169 to i64
  %arrayidx171 = getelementptr inbounds double, double* %grid, i64 %idxprom170
  %i45 = load double, double* %arrayidx171, align 8
  %add172 = add nsw i32 6, %i.0
  %idxprom173 = sext i32 %add172 to i64
  %arrayidx174 = getelementptr inbounds double, double* %grid, i64 %idxprom173
  %i46 = load double, double* %arrayidx174, align 8
  %sub175 = fsub double %i45, %i46
  %add176 = add nsw i32 11, %i.0
  %idxprom177 = sext i32 %add176 to i64
  %arrayidx178 = getelementptr inbounds double, double* %grid, i64 %idxprom177
  %i47 = load double, double* %arrayidx178, align 8
  %add179 = fadd double %sub175, %i47
  %add180 = add nsw i32 12, %i.0
  %idxprom181 = sext i32 %add180 to i64
  %arrayidx182 = getelementptr inbounds double, double* %grid, i64 %idxprom181
  %i48 = load double, double* %arrayidx182, align 8
  %sub183 = fsub double %add179, %i48
  %add184 = add nsw i32 13, %i.0
  %idxprom185 = sext i32 %add184 to i64
  %arrayidx186 = getelementptr inbounds double, double* %grid, i64 %idxprom185
  %i49 = load double, double* %arrayidx186, align 8
  %add187 = fadd double %sub183, %i49
  %add188 = add nsw i32 14, %i.0
  %idxprom189 = sext i32 %add188 to i64
  %arrayidx190 = getelementptr inbounds double, double* %grid, i64 %idxprom189
  %i50 = load double, double* %arrayidx190, align 8
  %sub191 = fsub double %add187, %i50
  %add192 = add nsw i32 15, %i.0
  %idxprom193 = sext i32 %add192 to i64
  %arrayidx194 = getelementptr inbounds double, double* %grid, i64 %idxprom193
  %i51 = load double, double* %arrayidx194, align 8
  %add195 = fadd double %sub191, %i51
  %add196 = add nsw i32 16, %i.0
  %idxprom197 = sext i32 %add196 to i64
  %arrayidx198 = getelementptr inbounds double, double* %grid, i64 %idxprom197
  %i52 = load double, double* %arrayidx198, align 8
  %sub199 = fsub double %add195, %i52
  %add200 = add nsw i32 17, %i.0
  %idxprom201 = sext i32 %add200 to i64
  %arrayidx202 = getelementptr inbounds double, double* %grid, i64 %idxprom201
  %i53 = load double, double* %arrayidx202, align 8
  %add203 = fadd double %sub199, %i53
  %add204 = add nsw i32 18, %i.0
  %idxprom205 = sext i32 %add204 to i64
  %arrayidx206 = getelementptr inbounds double, double* %grid, i64 %idxprom205
  %i54 = load double, double* %arrayidx206, align 8
  %sub207 = fsub double %add203, %i54
  %mul = fmul double %sub129, %sub129
  %mul208 = fmul double %sub168, %sub168
  %add209 = fadd double %mul, %mul208
  %mul210 = fmul double %sub207, %sub207
  %add211 = fadd double %add209, %mul210
  %mul212 = fmul double %add72, %add72
  %div = fdiv double %add211, %mul212
  %cmp213 = fcmp olt double %div, %minU2.0
  br i1 %cmp213, label %if.then214, label %if.end215

if.then214:                                       ; preds = %if.end91
  br label %if.end215

if.end215:                                        ; preds = %if.then214, %if.end91
  %minU2.1 = phi double [ %div, %if.then214 ], [ %minU2.0, %if.end91 ]
  %cmp216 = fcmp ogt double %div, %maxU2.0
  br i1 %cmp216, label %if.then217, label %if.end218

if.then217:                                       ; preds = %if.end215
  br label %if.end218

if.end218:                                        ; preds = %if.then217, %if.end215
  %maxU2.1 = phi double [ %div, %if.then217 ], [ %maxU2.0, %if.end215 ]
  br label %if.end219

if.end219:                                        ; preds = %if.end218, %if.then81
  %maxU2.2 = phi double [ %maxU2.0, %if.then81 ], [ %maxU2.1, %if.end218 ]
  %minU2.2 = phi double [ %minU2.0, %if.then81 ], [ %minU2.1, %if.end218 ]
  %nFluidCells.2 = phi i32 [ %nFluidCells.0, %if.then81 ], [ %nFluidCells.1, %if.end218 ]
  %nAccelCells.2 = phi i32 [ %nAccelCells.0, %if.then81 ], [ %nAccelCells.1, %if.end218 ]
  %nObstacleCells.1 = phi i32 [ %inc, %if.then81 ], [ %nObstacleCells.0, %if.end218 ]
  br label %for.inc

for.inc:                                          ; preds = %if.end219
  %add220 = add nsw i32 %i.0, 20
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %call = call double @sqrt(double %minU2.0) #6
  %call221 = call double @sqrt(double %maxU2.0) #6
  %call222 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([138 x i8], [138 x i8]* @.str.2, i64 0, i64 0), i32 %nObstacleCells.0, i32 %nAccelCells.0, i32 %nFluidCells.0, double %minRho.0, double %maxRho.0, double %mass.0, double %call, double %call221)
  ret void
}

; Function Attrs: nounwind
declare dso_local double @sqrt(double) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_storeVelocityField(double* %grid, i8* %filename, i32 %binary) #0 {
entry:
  %ux = alloca float, align 4
  %uy = alloca float, align 4
  %uz = alloca float, align 4
  %tobool = icmp ne i32 %binary, 0
  %i = zext i1 %tobool to i64
  %cond = select i1 %tobool, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.4, i64 0, i64 0)
  %call = call noalias %struct._IO_FILE* @fopen(i8* %filename, i8* %cond)
  br label %for.cond

for.cond:                                         ; preds = %for.inc501, %entry
  %z.0 = phi i32 [ 0, %entry ], [ %inc502, %for.inc501 ]
  %cmp = icmp slt i32 %z.0, 130
  br i1 %cmp, label %for.body, label %for.end503

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc498, %for.body
  %y.0 = phi i32 [ 0, %for.body ], [ %inc499, %for.inc498 ]
  %cmp2 = icmp slt i32 %y.0, 100
  br i1 %cmp2, label %for.body3, label %for.end500

for.body3:                                        ; preds = %for.cond1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body3
  %x.0 = phi i32 [ 0, %for.body3 ], [ %inc, %for.inc ]
  %cmp5 = icmp slt i32 %x.0, 100
  br i1 %cmp5, label %for.body6, label %for.end

for.body6:                                        ; preds = %for.cond4
  %mul = mul nsw i32 %y.0, 100
  %add = add nsw i32 %x.0, %mul
  %mul7 = mul nsw i32 %z.0, 100
  %mul8 = mul nsw i32 %mul7, 100
  %add9 = add nsw i32 %add, %mul8
  %mul10 = mul nsw i32 20, %add9
  %add11 = add nsw i32 0, %mul10
  %idxprom = sext i32 %add11 to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  %i1 = load double, double* %arrayidx, align 8
  %mul12 = mul nsw i32 %y.0, 100
  %add13 = add nsw i32 %x.0, %mul12
  %mul14 = mul nsw i32 %z.0, 100
  %mul15 = mul nsw i32 %mul14, 100
  %add16 = add nsw i32 %add13, %mul15
  %mul17 = mul nsw i32 20, %add16
  %add18 = add nsw i32 1, %mul17
  %idxprom19 = sext i32 %add18 to i64
  %arrayidx20 = getelementptr inbounds double, double* %grid, i64 %idxprom19
  %i2 = load double, double* %arrayidx20, align 8
  %add21 = fadd double %i1, %i2
  %mul22 = mul nsw i32 %y.0, 100
  %add23 = add nsw i32 %x.0, %mul22
  %mul24 = mul nsw i32 %z.0, 100
  %mul25 = mul nsw i32 %mul24, 100
  %add26 = add nsw i32 %add23, %mul25
  %mul27 = mul nsw i32 20, %add26
  %add28 = add nsw i32 2, %mul27
  %idxprom29 = sext i32 %add28 to i64
  %arrayidx30 = getelementptr inbounds double, double* %grid, i64 %idxprom29
  %i3 = load double, double* %arrayidx30, align 8
  %add31 = fadd double %add21, %i3
  %mul32 = mul nsw i32 %y.0, 100
  %add33 = add nsw i32 %x.0, %mul32
  %mul34 = mul nsw i32 %z.0, 100
  %mul35 = mul nsw i32 %mul34, 100
  %add36 = add nsw i32 %add33, %mul35
  %mul37 = mul nsw i32 20, %add36
  %add38 = add nsw i32 3, %mul37
  %idxprom39 = sext i32 %add38 to i64
  %arrayidx40 = getelementptr inbounds double, double* %grid, i64 %idxprom39
  %i4 = load double, double* %arrayidx40, align 8
  %add41 = fadd double %add31, %i4
  %mul42 = mul nsw i32 %y.0, 100
  %add43 = add nsw i32 %x.0, %mul42
  %mul44 = mul nsw i32 %z.0, 100
  %mul45 = mul nsw i32 %mul44, 100
  %add46 = add nsw i32 %add43, %mul45
  %mul47 = mul nsw i32 20, %add46
  %add48 = add nsw i32 4, %mul47
  %idxprom49 = sext i32 %add48 to i64
  %arrayidx50 = getelementptr inbounds double, double* %grid, i64 %idxprom49
  %i5 = load double, double* %arrayidx50, align 8
  %add51 = fadd double %add41, %i5
  %mul52 = mul nsw i32 %y.0, 100
  %add53 = add nsw i32 %x.0, %mul52
  %mul54 = mul nsw i32 %z.0, 100
  %mul55 = mul nsw i32 %mul54, 100
  %add56 = add nsw i32 %add53, %mul55
  %mul57 = mul nsw i32 20, %add56
  %add58 = add nsw i32 5, %mul57
  %idxprom59 = sext i32 %add58 to i64
  %arrayidx60 = getelementptr inbounds double, double* %grid, i64 %idxprom59
  %i6 = load double, double* %arrayidx60, align 8
  %add61 = fadd double %add51, %i6
  %mul62 = mul nsw i32 %y.0, 100
  %add63 = add nsw i32 %x.0, %mul62
  %mul64 = mul nsw i32 %z.0, 100
  %mul65 = mul nsw i32 %mul64, 100
  %add66 = add nsw i32 %add63, %mul65
  %mul67 = mul nsw i32 20, %add66
  %add68 = add nsw i32 6, %mul67
  %idxprom69 = sext i32 %add68 to i64
  %arrayidx70 = getelementptr inbounds double, double* %grid, i64 %idxprom69
  %i7 = load double, double* %arrayidx70, align 8
  %add71 = fadd double %add61, %i7
  %mul72 = mul nsw i32 %y.0, 100
  %add73 = add nsw i32 %x.0, %mul72
  %mul74 = mul nsw i32 %z.0, 100
  %mul75 = mul nsw i32 %mul74, 100
  %add76 = add nsw i32 %add73, %mul75
  %mul77 = mul nsw i32 20, %add76
  %add78 = add nsw i32 7, %mul77
  %idxprom79 = sext i32 %add78 to i64
  %arrayidx80 = getelementptr inbounds double, double* %grid, i64 %idxprom79
  %i8 = load double, double* %arrayidx80, align 8
  %add81 = fadd double %add71, %i8
  %mul82 = mul nsw i32 %y.0, 100
  %add83 = add nsw i32 %x.0, %mul82
  %mul84 = mul nsw i32 %z.0, 100
  %mul85 = mul nsw i32 %mul84, 100
  %add86 = add nsw i32 %add83, %mul85
  %mul87 = mul nsw i32 20, %add86
  %add88 = add nsw i32 8, %mul87
  %idxprom89 = sext i32 %add88 to i64
  %arrayidx90 = getelementptr inbounds double, double* %grid, i64 %idxprom89
  %i9 = load double, double* %arrayidx90, align 8
  %add91 = fadd double %add81, %i9
  %mul92 = mul nsw i32 %y.0, 100
  %add93 = add nsw i32 %x.0, %mul92
  %mul94 = mul nsw i32 %z.0, 100
  %mul95 = mul nsw i32 %mul94, 100
  %add96 = add nsw i32 %add93, %mul95
  %mul97 = mul nsw i32 20, %add96
  %add98 = add nsw i32 9, %mul97
  %idxprom99 = sext i32 %add98 to i64
  %arrayidx100 = getelementptr inbounds double, double* %grid, i64 %idxprom99
  %i10 = load double, double* %arrayidx100, align 8
  %add101 = fadd double %add91, %i10
  %mul102 = mul nsw i32 %y.0, 100
  %add103 = add nsw i32 %x.0, %mul102
  %mul104 = mul nsw i32 %z.0, 100
  %mul105 = mul nsw i32 %mul104, 100
  %add106 = add nsw i32 %add103, %mul105
  %mul107 = mul nsw i32 20, %add106
  %add108 = add nsw i32 10, %mul107
  %idxprom109 = sext i32 %add108 to i64
  %arrayidx110 = getelementptr inbounds double, double* %grid, i64 %idxprom109
  %i11 = load double, double* %arrayidx110, align 8
  %add111 = fadd double %add101, %i11
  %mul112 = mul nsw i32 %y.0, 100
  %add113 = add nsw i32 %x.0, %mul112
  %mul114 = mul nsw i32 %z.0, 100
  %mul115 = mul nsw i32 %mul114, 100
  %add116 = add nsw i32 %add113, %mul115
  %mul117 = mul nsw i32 20, %add116
  %add118 = add nsw i32 11, %mul117
  %idxprom119 = sext i32 %add118 to i64
  %arrayidx120 = getelementptr inbounds double, double* %grid, i64 %idxprom119
  %i12 = load double, double* %arrayidx120, align 8
  %add121 = fadd double %add111, %i12
  %mul122 = mul nsw i32 %y.0, 100
  %add123 = add nsw i32 %x.0, %mul122
  %mul124 = mul nsw i32 %z.0, 100
  %mul125 = mul nsw i32 %mul124, 100
  %add126 = add nsw i32 %add123, %mul125
  %mul127 = mul nsw i32 20, %add126
  %add128 = add nsw i32 12, %mul127
  %idxprom129 = sext i32 %add128 to i64
  %arrayidx130 = getelementptr inbounds double, double* %grid, i64 %idxprom129
  %i13 = load double, double* %arrayidx130, align 8
  %add131 = fadd double %add121, %i13
  %mul132 = mul nsw i32 %y.0, 100
  %add133 = add nsw i32 %x.0, %mul132
  %mul134 = mul nsw i32 %z.0, 100
  %mul135 = mul nsw i32 %mul134, 100
  %add136 = add nsw i32 %add133, %mul135
  %mul137 = mul nsw i32 20, %add136
  %add138 = add nsw i32 13, %mul137
  %idxprom139 = sext i32 %add138 to i64
  %arrayidx140 = getelementptr inbounds double, double* %grid, i64 %idxprom139
  %i14 = load double, double* %arrayidx140, align 8
  %add141 = fadd double %add131, %i14
  %mul142 = mul nsw i32 %y.0, 100
  %add143 = add nsw i32 %x.0, %mul142
  %mul144 = mul nsw i32 %z.0, 100
  %mul145 = mul nsw i32 %mul144, 100
  %add146 = add nsw i32 %add143, %mul145
  %mul147 = mul nsw i32 20, %add146
  %add148 = add nsw i32 14, %mul147
  %idxprom149 = sext i32 %add148 to i64
  %arrayidx150 = getelementptr inbounds double, double* %grid, i64 %idxprom149
  %i15 = load double, double* %arrayidx150, align 8
  %add151 = fadd double %add141, %i15
  %mul152 = mul nsw i32 %y.0, 100
  %add153 = add nsw i32 %x.0, %mul152
  %mul154 = mul nsw i32 %z.0, 100
  %mul155 = mul nsw i32 %mul154, 100
  %add156 = add nsw i32 %add153, %mul155
  %mul157 = mul nsw i32 20, %add156
  %add158 = add nsw i32 15, %mul157
  %idxprom159 = sext i32 %add158 to i64
  %arrayidx160 = getelementptr inbounds double, double* %grid, i64 %idxprom159
  %i16 = load double, double* %arrayidx160, align 8
  %add161 = fadd double %add151, %i16
  %mul162 = mul nsw i32 %y.0, 100
  %add163 = add nsw i32 %x.0, %mul162
  %mul164 = mul nsw i32 %z.0, 100
  %mul165 = mul nsw i32 %mul164, 100
  %add166 = add nsw i32 %add163, %mul165
  %mul167 = mul nsw i32 20, %add166
  %add168 = add nsw i32 16, %mul167
  %idxprom169 = sext i32 %add168 to i64
  %arrayidx170 = getelementptr inbounds double, double* %grid, i64 %idxprom169
  %i17 = load double, double* %arrayidx170, align 8
  %add171 = fadd double %add161, %i17
  %mul172 = mul nsw i32 %y.0, 100
  %add173 = add nsw i32 %x.0, %mul172
  %mul174 = mul nsw i32 %z.0, 100
  %mul175 = mul nsw i32 %mul174, 100
  %add176 = add nsw i32 %add173, %mul175
  %mul177 = mul nsw i32 20, %add176
  %add178 = add nsw i32 17, %mul177
  %idxprom179 = sext i32 %add178 to i64
  %arrayidx180 = getelementptr inbounds double, double* %grid, i64 %idxprom179
  %i18 = load double, double* %arrayidx180, align 8
  %add181 = fadd double %add171, %i18
  %mul182 = mul nsw i32 %y.0, 100
  %add183 = add nsw i32 %x.0, %mul182
  %mul184 = mul nsw i32 %z.0, 100
  %mul185 = mul nsw i32 %mul184, 100
  %add186 = add nsw i32 %add183, %mul185
  %mul187 = mul nsw i32 20, %add186
  %add188 = add nsw i32 18, %mul187
  %idxprom189 = sext i32 %add188 to i64
  %arrayidx190 = getelementptr inbounds double, double* %grid, i64 %idxprom189
  %i19 = load double, double* %arrayidx190, align 8
  %add191 = fadd double %add181, %i19
  %conv = fptrunc double %add191 to float
  %mul192 = mul nsw i32 %y.0, 100
  %add193 = add nsw i32 %x.0, %mul192
  %mul194 = mul nsw i32 %z.0, 100
  %mul195 = mul nsw i32 %mul194, 100
  %add196 = add nsw i32 %add193, %mul195
  %mul197 = mul nsw i32 20, %add196
  %add198 = add nsw i32 3, %mul197
  %idxprom199 = sext i32 %add198 to i64
  %arrayidx200 = getelementptr inbounds double, double* %grid, i64 %idxprom199
  %i20 = load double, double* %arrayidx200, align 8
  %mul201 = mul nsw i32 %y.0, 100
  %add202 = add nsw i32 %x.0, %mul201
  %mul203 = mul nsw i32 %z.0, 100
  %mul204 = mul nsw i32 %mul203, 100
  %add205 = add nsw i32 %add202, %mul204
  %mul206 = mul nsw i32 20, %add205
  %add207 = add nsw i32 4, %mul206
  %idxprom208 = sext i32 %add207 to i64
  %arrayidx209 = getelementptr inbounds double, double* %grid, i64 %idxprom208
  %i21 = load double, double* %arrayidx209, align 8
  %sub = fsub double %i20, %i21
  %mul210 = mul nsw i32 %y.0, 100
  %add211 = add nsw i32 %x.0, %mul210
  %mul212 = mul nsw i32 %z.0, 100
  %mul213 = mul nsw i32 %mul212, 100
  %add214 = add nsw i32 %add211, %mul213
  %mul215 = mul nsw i32 20, %add214
  %add216 = add nsw i32 7, %mul215
  %idxprom217 = sext i32 %add216 to i64
  %arrayidx218 = getelementptr inbounds double, double* %grid, i64 %idxprom217
  %i22 = load double, double* %arrayidx218, align 8
  %add219 = fadd double %sub, %i22
  %mul220 = mul nsw i32 %y.0, 100
  %add221 = add nsw i32 %x.0, %mul220
  %mul222 = mul nsw i32 %z.0, 100
  %mul223 = mul nsw i32 %mul222, 100
  %add224 = add nsw i32 %add221, %mul223
  %mul225 = mul nsw i32 20, %add224
  %add226 = add nsw i32 8, %mul225
  %idxprom227 = sext i32 %add226 to i64
  %arrayidx228 = getelementptr inbounds double, double* %grid, i64 %idxprom227
  %i23 = load double, double* %arrayidx228, align 8
  %sub229 = fsub double %add219, %i23
  %mul230 = mul nsw i32 %y.0, 100
  %add231 = add nsw i32 %x.0, %mul230
  %mul232 = mul nsw i32 %z.0, 100
  %mul233 = mul nsw i32 %mul232, 100
  %add234 = add nsw i32 %add231, %mul233
  %mul235 = mul nsw i32 20, %add234
  %add236 = add nsw i32 9, %mul235
  %idxprom237 = sext i32 %add236 to i64
  %arrayidx238 = getelementptr inbounds double, double* %grid, i64 %idxprom237
  %i24 = load double, double* %arrayidx238, align 8
  %add239 = fadd double %sub229, %i24
  %mul240 = mul nsw i32 %y.0, 100
  %add241 = add nsw i32 %x.0, %mul240
  %mul242 = mul nsw i32 %z.0, 100
  %mul243 = mul nsw i32 %mul242, 100
  %add244 = add nsw i32 %add241, %mul243
  %mul245 = mul nsw i32 20, %add244
  %add246 = add nsw i32 10, %mul245
  %idxprom247 = sext i32 %add246 to i64
  %arrayidx248 = getelementptr inbounds double, double* %grid, i64 %idxprom247
  %i25 = load double, double* %arrayidx248, align 8
  %sub249 = fsub double %add239, %i25
  %mul250 = mul nsw i32 %y.0, 100
  %add251 = add nsw i32 %x.0, %mul250
  %mul252 = mul nsw i32 %z.0, 100
  %mul253 = mul nsw i32 %mul252, 100
  %add254 = add nsw i32 %add251, %mul253
  %mul255 = mul nsw i32 20, %add254
  %add256 = add nsw i32 15, %mul255
  %idxprom257 = sext i32 %add256 to i64
  %arrayidx258 = getelementptr inbounds double, double* %grid, i64 %idxprom257
  %i26 = load double, double* %arrayidx258, align 8
  %add259 = fadd double %sub249, %i26
  %mul260 = mul nsw i32 %y.0, 100
  %add261 = add nsw i32 %x.0, %mul260
  %mul262 = mul nsw i32 %z.0, 100
  %mul263 = mul nsw i32 %mul262, 100
  %add264 = add nsw i32 %add261, %mul263
  %mul265 = mul nsw i32 20, %add264
  %add266 = add nsw i32 16, %mul265
  %idxprom267 = sext i32 %add266 to i64
  %arrayidx268 = getelementptr inbounds double, double* %grid, i64 %idxprom267
  %i27 = load double, double* %arrayidx268, align 8
  %add269 = fadd double %add259, %i27
  %mul270 = mul nsw i32 %y.0, 100
  %add271 = add nsw i32 %x.0, %mul270
  %mul272 = mul nsw i32 %z.0, 100
  %mul273 = mul nsw i32 %mul272, 100
  %add274 = add nsw i32 %add271, %mul273
  %mul275 = mul nsw i32 20, %add274
  %add276 = add nsw i32 17, %mul275
  %idxprom277 = sext i32 %add276 to i64
  %arrayidx278 = getelementptr inbounds double, double* %grid, i64 %idxprom277
  %i28 = load double, double* %arrayidx278, align 8
  %sub279 = fsub double %add269, %i28
  %mul280 = mul nsw i32 %y.0, 100
  %add281 = add nsw i32 %x.0, %mul280
  %mul282 = mul nsw i32 %z.0, 100
  %mul283 = mul nsw i32 %mul282, 100
  %add284 = add nsw i32 %add281, %mul283
  %mul285 = mul nsw i32 20, %add284
  %add286 = add nsw i32 18, %mul285
  %idxprom287 = sext i32 %add286 to i64
  %arrayidx288 = getelementptr inbounds double, double* %grid, i64 %idxprom287
  %i29 = load double, double* %arrayidx288, align 8
  %sub289 = fsub double %sub279, %i29
  %conv290 = fptrunc double %sub289 to float
  store float %conv290, float* %ux, align 4
  %mul291 = mul nsw i32 %y.0, 100
  %add292 = add nsw i32 %x.0, %mul291
  %mul293 = mul nsw i32 %z.0, 100
  %mul294 = mul nsw i32 %mul293, 100
  %add295 = add nsw i32 %add292, %mul294
  %mul296 = mul nsw i32 20, %add295
  %add297 = add nsw i32 1, %mul296
  %idxprom298 = sext i32 %add297 to i64
  %arrayidx299 = getelementptr inbounds double, double* %grid, i64 %idxprom298
  %i30 = load double, double* %arrayidx299, align 8
  %mul300 = mul nsw i32 %y.0, 100
  %add301 = add nsw i32 %x.0, %mul300
  %mul302 = mul nsw i32 %z.0, 100
  %mul303 = mul nsw i32 %mul302, 100
  %add304 = add nsw i32 %add301, %mul303
  %mul305 = mul nsw i32 20, %add304
  %add306 = add nsw i32 2, %mul305
  %idxprom307 = sext i32 %add306 to i64
  %arrayidx308 = getelementptr inbounds double, double* %grid, i64 %idxprom307
  %i31 = load double, double* %arrayidx308, align 8
  %sub309 = fsub double %i30, %i31
  %mul310 = mul nsw i32 %y.0, 100
  %add311 = add nsw i32 %x.0, %mul310
  %mul312 = mul nsw i32 %z.0, 100
  %mul313 = mul nsw i32 %mul312, 100
  %add314 = add nsw i32 %add311, %mul313
  %mul315 = mul nsw i32 20, %add314
  %add316 = add nsw i32 7, %mul315
  %idxprom317 = sext i32 %add316 to i64
  %arrayidx318 = getelementptr inbounds double, double* %grid, i64 %idxprom317
  %i32 = load double, double* %arrayidx318, align 8
  %add319 = fadd double %sub309, %i32
  %mul320 = mul nsw i32 %y.0, 100
  %add321 = add nsw i32 %x.0, %mul320
  %mul322 = mul nsw i32 %z.0, 100
  %mul323 = mul nsw i32 %mul322, 100
  %add324 = add nsw i32 %add321, %mul323
  %mul325 = mul nsw i32 20, %add324
  %add326 = add nsw i32 8, %mul325
  %idxprom327 = sext i32 %add326 to i64
  %arrayidx328 = getelementptr inbounds double, double* %grid, i64 %idxprom327
  %i33 = load double, double* %arrayidx328, align 8
  %add329 = fadd double %add319, %i33
  %mul330 = mul nsw i32 %y.0, 100
  %add331 = add nsw i32 %x.0, %mul330
  %mul332 = mul nsw i32 %z.0, 100
  %mul333 = mul nsw i32 %mul332, 100
  %add334 = add nsw i32 %add331, %mul333
  %mul335 = mul nsw i32 20, %add334
  %add336 = add nsw i32 9, %mul335
  %idxprom337 = sext i32 %add336 to i64
  %arrayidx338 = getelementptr inbounds double, double* %grid, i64 %idxprom337
  %i34 = load double, double* %arrayidx338, align 8
  %sub339 = fsub double %add329, %i34
  %mul340 = mul nsw i32 %y.0, 100
  %add341 = add nsw i32 %x.0, %mul340
  %mul342 = mul nsw i32 %z.0, 100
  %mul343 = mul nsw i32 %mul342, 100
  %add344 = add nsw i32 %add341, %mul343
  %mul345 = mul nsw i32 20, %add344
  %add346 = add nsw i32 10, %mul345
  %idxprom347 = sext i32 %add346 to i64
  %arrayidx348 = getelementptr inbounds double, double* %grid, i64 %idxprom347
  %i35 = load double, double* %arrayidx348, align 8
  %sub349 = fsub double %sub339, %i35
  %mul350 = mul nsw i32 %y.0, 100
  %add351 = add nsw i32 %x.0, %mul350
  %mul352 = mul nsw i32 %z.0, 100
  %mul353 = mul nsw i32 %mul352, 100
  %add354 = add nsw i32 %add351, %mul353
  %mul355 = mul nsw i32 20, %add354
  %add356 = add nsw i32 11, %mul355
  %idxprom357 = sext i32 %add356 to i64
  %arrayidx358 = getelementptr inbounds double, double* %grid, i64 %idxprom357
  %i36 = load double, double* %arrayidx358, align 8
  %add359 = fadd double %sub349, %i36
  %mul360 = mul nsw i32 %y.0, 100
  %add361 = add nsw i32 %x.0, %mul360
  %mul362 = mul nsw i32 %z.0, 100
  %mul363 = mul nsw i32 %mul362, 100
  %add364 = add nsw i32 %add361, %mul363
  %mul365 = mul nsw i32 20, %add364
  %add366 = add nsw i32 12, %mul365
  %idxprom367 = sext i32 %add366 to i64
  %arrayidx368 = getelementptr inbounds double, double* %grid, i64 %idxprom367
  %i37 = load double, double* %arrayidx368, align 8
  %add369 = fadd double %add359, %i37
  %mul370 = mul nsw i32 %y.0, 100
  %add371 = add nsw i32 %x.0, %mul370
  %mul372 = mul nsw i32 %z.0, 100
  %mul373 = mul nsw i32 %mul372, 100
  %add374 = add nsw i32 %add371, %mul373
  %mul375 = mul nsw i32 20, %add374
  %add376 = add nsw i32 13, %mul375
  %idxprom377 = sext i32 %add376 to i64
  %arrayidx378 = getelementptr inbounds double, double* %grid, i64 %idxprom377
  %i38 = load double, double* %arrayidx378, align 8
  %sub379 = fsub double %add369, %i38
  %mul380 = mul nsw i32 %y.0, 100
  %add381 = add nsw i32 %x.0, %mul380
  %mul382 = mul nsw i32 %z.0, 100
  %mul383 = mul nsw i32 %mul382, 100
  %add384 = add nsw i32 %add381, %mul383
  %mul385 = mul nsw i32 20, %add384
  %add386 = add nsw i32 14, %mul385
  %idxprom387 = sext i32 %add386 to i64
  %arrayidx388 = getelementptr inbounds double, double* %grid, i64 %idxprom387
  %i39 = load double, double* %arrayidx388, align 8
  %sub389 = fsub double %sub379, %i39
  %conv390 = fptrunc double %sub389 to float
  store float %conv390, float* %uy, align 4
  %mul391 = mul nsw i32 %y.0, 100
  %add392 = add nsw i32 %x.0, %mul391
  %mul393 = mul nsw i32 %z.0, 100
  %mul394 = mul nsw i32 %mul393, 100
  %add395 = add nsw i32 %add392, %mul394
  %mul396 = mul nsw i32 20, %add395
  %add397 = add nsw i32 5, %mul396
  %idxprom398 = sext i32 %add397 to i64
  %arrayidx399 = getelementptr inbounds double, double* %grid, i64 %idxprom398
  %i40 = load double, double* %arrayidx399, align 8
  %mul400 = mul nsw i32 %y.0, 100
  %add401 = add nsw i32 %x.0, %mul400
  %mul402 = mul nsw i32 %z.0, 100
  %mul403 = mul nsw i32 %mul402, 100
  %add404 = add nsw i32 %add401, %mul403
  %mul405 = mul nsw i32 20, %add404
  %add406 = add nsw i32 6, %mul405
  %idxprom407 = sext i32 %add406 to i64
  %arrayidx408 = getelementptr inbounds double, double* %grid, i64 %idxprom407
  %i41 = load double, double* %arrayidx408, align 8
  %sub409 = fsub double %i40, %i41
  %mul410 = mul nsw i32 %y.0, 100
  %add411 = add nsw i32 %x.0, %mul410
  %mul412 = mul nsw i32 %z.0, 100
  %mul413 = mul nsw i32 %mul412, 100
  %add414 = add nsw i32 %add411, %mul413
  %mul415 = mul nsw i32 20, %add414
  %add416 = add nsw i32 11, %mul415
  %idxprom417 = sext i32 %add416 to i64
  %arrayidx418 = getelementptr inbounds double, double* %grid, i64 %idxprom417
  %i42 = load double, double* %arrayidx418, align 8
  %add419 = fadd double %sub409, %i42
  %mul420 = mul nsw i32 %y.0, 100
  %add421 = add nsw i32 %x.0, %mul420
  %mul422 = mul nsw i32 %z.0, 100
  %mul423 = mul nsw i32 %mul422, 100
  %add424 = add nsw i32 %add421, %mul423
  %mul425 = mul nsw i32 20, %add424
  %add426 = add nsw i32 12, %mul425
  %idxprom427 = sext i32 %add426 to i64
  %arrayidx428 = getelementptr inbounds double, double* %grid, i64 %idxprom427
  %i43 = load double, double* %arrayidx428, align 8
  %sub429 = fsub double %add419, %i43
  %mul430 = mul nsw i32 %y.0, 100
  %add431 = add nsw i32 %x.0, %mul430
  %mul432 = mul nsw i32 %z.0, 100
  %mul433 = mul nsw i32 %mul432, 100
  %add434 = add nsw i32 %add431, %mul433
  %mul435 = mul nsw i32 20, %add434
  %add436 = add nsw i32 13, %mul435
  %idxprom437 = sext i32 %add436 to i64
  %arrayidx438 = getelementptr inbounds double, double* %grid, i64 %idxprom437
  %i44 = load double, double* %arrayidx438, align 8
  %add439 = fadd double %sub429, %i44
  %mul440 = mul nsw i32 %y.0, 100
  %add441 = add nsw i32 %x.0, %mul440
  %mul442 = mul nsw i32 %z.0, 100
  %mul443 = mul nsw i32 %mul442, 100
  %add444 = add nsw i32 %add441, %mul443
  %mul445 = mul nsw i32 20, %add444
  %add446 = add nsw i32 14, %mul445
  %idxprom447 = sext i32 %add446 to i64
  %arrayidx448 = getelementptr inbounds double, double* %grid, i64 %idxprom447
  %i45 = load double, double* %arrayidx448, align 8
  %sub449 = fsub double %add439, %i45
  %mul450 = mul nsw i32 %y.0, 100
  %add451 = add nsw i32 %x.0, %mul450
  %mul452 = mul nsw i32 %z.0, 100
  %mul453 = mul nsw i32 %mul452, 100
  %add454 = add nsw i32 %add451, %mul453
  %mul455 = mul nsw i32 20, %add454
  %add456 = add nsw i32 15, %mul455
  %idxprom457 = sext i32 %add456 to i64
  %arrayidx458 = getelementptr inbounds double, double* %grid, i64 %idxprom457
  %i46 = load double, double* %arrayidx458, align 8
  %add459 = fadd double %sub449, %i46
  %mul460 = mul nsw i32 %y.0, 100
  %add461 = add nsw i32 %x.0, %mul460
  %mul462 = mul nsw i32 %z.0, 100
  %mul463 = mul nsw i32 %mul462, 100
  %add464 = add nsw i32 %add461, %mul463
  %mul465 = mul nsw i32 20, %add464
  %add466 = add nsw i32 16, %mul465
  %idxprom467 = sext i32 %add466 to i64
  %arrayidx468 = getelementptr inbounds double, double* %grid, i64 %idxprom467
  %i47 = load double, double* %arrayidx468, align 8
  %sub469 = fsub double %add459, %i47
  %mul470 = mul nsw i32 %y.0, 100
  %add471 = add nsw i32 %x.0, %mul470
  %mul472 = mul nsw i32 %z.0, 100
  %mul473 = mul nsw i32 %mul472, 100
  %add474 = add nsw i32 %add471, %mul473
  %mul475 = mul nsw i32 20, %add474
  %add476 = add nsw i32 17, %mul475
  %idxprom477 = sext i32 %add476 to i64
  %arrayidx478 = getelementptr inbounds double, double* %grid, i64 %idxprom477
  %i48 = load double, double* %arrayidx478, align 8
  %add479 = fadd double %sub469, %i48
  %mul480 = mul nsw i32 %y.0, 100
  %add481 = add nsw i32 %x.0, %mul480
  %mul482 = mul nsw i32 %z.0, 100
  %mul483 = mul nsw i32 %mul482, 100
  %add484 = add nsw i32 %add481, %mul483
  %mul485 = mul nsw i32 20, %add484
  %add486 = add nsw i32 18, %mul485
  %idxprom487 = sext i32 %add486 to i64
  %arrayidx488 = getelementptr inbounds double, double* %grid, i64 %idxprom487
  %i49 = load double, double* %arrayidx488, align 8
  %sub489 = fsub double %add479, %i49
  %conv490 = fptrunc double %sub489 to float
  store float %conv490, float* %uz, align 4
  %i50 = load float, float* %ux, align 4
  %div = fdiv float %i50, %conv
  store float %div, float* %ux, align 4
  %i51 = load float, float* %uy, align 4
  %div491 = fdiv float %i51, %conv
  store float %div491, float* %uy, align 4
  %i52 = load float, float* %uz, align 4
  %div492 = fdiv float %i52, %conv
  store float %div492, float* %uz, align 4
  %tobool493 = icmp ne i32 %binary, 0
  br i1 %tobool493, label %if.then, label %if.else

if.then:                                          ; preds = %for.body6
  call void @storeValue(%struct._IO_FILE* %call, float* %ux)
  call void @storeValue(%struct._IO_FILE* %call, float* %uy)
  call void @storeValue(%struct._IO_FILE* %call, float* %uz)
  br label %if.end

if.else:                                          ; preds = %for.body6
  %i53 = load float, float* %ux, align 4
  %conv494 = fpext float %i53 to double
  %i54 = load float, float* %uy, align 4
  %conv495 = fpext float %i54 to double
  %i55 = load float, float* %uz, align 4
  %conv496 = fpext float %i55 to double
  %call497 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %call, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.5, i64 0, i64 0), double %conv494, double %conv495, double %conv496)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %inc = add nsw i32 %x.0, 1
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  br label %for.inc498

for.inc498:                                       ; preds = %for.end
  %inc499 = add nsw i32 %y.0, 1
  br label %for.cond1

for.end500:                                       ; preds = %for.cond1
  br label %for.inc501

for.inc501:                                       ; preds = %for.end500
  %inc502 = add nsw i32 %z.0, 1
  br label %for.cond

for.end503:                                       ; preds = %for.cond
  %call504 = call i32 @fclose(%struct._IO_FILE* %call)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal void @storeValue(%struct._IO_FILE* %file, float* %v) #0 {
entry:
  %litteBigEndianTest = alloca i32, align 4
  %buffer = alloca [4 x i8], align 1
  store i32 1, i32* %litteBigEndianTest, align 4
  %i = bitcast i32* %litteBigEndianTest to i8*
  %i1 = load i8, i8* %i, align 4
  %conv = zext i8 %i1 to i32
  %cmp = icmp eq i32 %conv, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i2 = bitcast float* %v to i8*
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.then
  %i.0 = phi i32 [ 0, %if.then ], [ %inc, %for.inc ]
  %conv2 = sext i32 %i.0 to i64
  %cmp3 = icmp ult i64 %conv2, 4
  br i1 %cmp3, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %conv5 = sext i32 %i.0 to i64
  %sub = sub i64 4, %conv5
  %sub6 = sub i64 %sub, 1
  %arrayidx = getelementptr inbounds i8, i8* %i2, i64 %sub6
  %i3 = load i8, i8* %arrayidx, align 1
  %idxprom = sext i32 %i.0 to i64
  %arrayidx7 = getelementptr inbounds [4 x i8], [4 x i8]* %buffer, i64 0, i64 %idxprom
  store i8 %i3, i8* %arrayidx7, align 1
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %arraydecay = getelementptr inbounds [4 x i8], [4 x i8]* %buffer, i64 0, i64 0
  %call = call i64 @fwrite(i8* %arraydecay, i64 4, i64 1, %struct._IO_FILE* %file)
  br label %if.end

if.else:                                          ; preds = %entry
  %i4 = bitcast float* %v to i8*
  %call8 = call i64 @fwrite(i8* %i4, i64 4, i64 1, %struct._IO_FILE* %file)
  br label %if.end

if.end:                                           ; preds = %if.else, %for.end
  ret void
}

declare dso_local i32 @fprintf(%struct._IO_FILE*, i8*, ...) #2

declare dso_local i64 @fwrite(i8*, i64, i64, %struct._IO_FILE*) #2

; Function Attrs: noinline nounwind uwtable
define dso_local void @LBM_compareVelocityField(double* %grid, i8* %filename, i32 %binary) #0 {
entry:
  %fileUx = alloca float, align 4
  %fileUy = alloca float, align 4
  %fileUz = alloca float, align 4
  %tobool = icmp ne i32 %binary, 0
  %i = zext i1 %tobool to i64
  %cond = select i1 %tobool, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.6, i64 0, i64 0)
  %call = call noalias %struct._IO_FILE* @fopen(i8* %filename, i8* %cond)
  br label %for.cond

for.cond:                                         ; preds = %for.inc512, %entry
  %z.0 = phi i32 [ 0, %entry ], [ %inc513, %for.inc512 ]
  %maxDiff2.0 = phi float [ 0xC6293E5940000000, %entry ], [ %maxDiff2.1, %for.inc512 ]
  %cmp = icmp slt i32 %z.0, 130
  br i1 %cmp, label %for.body, label %for.end514

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc509, %for.body
  %y.0 = phi i32 [ 0, %for.body ], [ %inc510, %for.inc509 ]
  %maxDiff2.1 = phi float [ %maxDiff2.0, %for.body ], [ %maxDiff2.2, %for.inc509 ]
  %cmp2 = icmp slt i32 %y.0, 100
  br i1 %cmp2, label %for.body3, label %for.end511

for.body3:                                        ; preds = %for.cond1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body3
  %x.0 = phi i32 [ 0, %for.body3 ], [ %inc, %for.inc ]
  %maxDiff2.2 = phi float [ %maxDiff2.1, %for.body3 ], [ %maxDiff2.3, %for.inc ]
  %cmp5 = icmp slt i32 %x.0, 100
  br i1 %cmp5, label %for.body6, label %for.end

for.body6:                                        ; preds = %for.cond4
  %mul = mul nsw i32 %y.0, 100
  %add = add nsw i32 %x.0, %mul
  %mul7 = mul nsw i32 %z.0, 100
  %mul8 = mul nsw i32 %mul7, 100
  %add9 = add nsw i32 %add, %mul8
  %mul10 = mul nsw i32 20, %add9
  %add11 = add nsw i32 0, %mul10
  %idxprom = sext i32 %add11 to i64
  %arrayidx = getelementptr inbounds double, double* %grid, i64 %idxprom
  %i1 = load double, double* %arrayidx, align 8
  %mul12 = mul nsw i32 %y.0, 100
  %add13 = add nsw i32 %x.0, %mul12
  %mul14 = mul nsw i32 %z.0, 100
  %mul15 = mul nsw i32 %mul14, 100
  %add16 = add nsw i32 %add13, %mul15
  %mul17 = mul nsw i32 20, %add16
  %add18 = add nsw i32 1, %mul17
  %idxprom19 = sext i32 %add18 to i64
  %arrayidx20 = getelementptr inbounds double, double* %grid, i64 %idxprom19
  %i2 = load double, double* %arrayidx20, align 8
  %add21 = fadd double %i1, %i2
  %mul22 = mul nsw i32 %y.0, 100
  %add23 = add nsw i32 %x.0, %mul22
  %mul24 = mul nsw i32 %z.0, 100
  %mul25 = mul nsw i32 %mul24, 100
  %add26 = add nsw i32 %add23, %mul25
  %mul27 = mul nsw i32 20, %add26
  %add28 = add nsw i32 2, %mul27
  %idxprom29 = sext i32 %add28 to i64
  %arrayidx30 = getelementptr inbounds double, double* %grid, i64 %idxprom29
  %i3 = load double, double* %arrayidx30, align 8
  %add31 = fadd double %add21, %i3
  %mul32 = mul nsw i32 %y.0, 100
  %add33 = add nsw i32 %x.0, %mul32
  %mul34 = mul nsw i32 %z.0, 100
  %mul35 = mul nsw i32 %mul34, 100
  %add36 = add nsw i32 %add33, %mul35
  %mul37 = mul nsw i32 20, %add36
  %add38 = add nsw i32 3, %mul37
  %idxprom39 = sext i32 %add38 to i64
  %arrayidx40 = getelementptr inbounds double, double* %grid, i64 %idxprom39
  %i4 = load double, double* %arrayidx40, align 8
  %add41 = fadd double %add31, %i4
  %mul42 = mul nsw i32 %y.0, 100
  %add43 = add nsw i32 %x.0, %mul42
  %mul44 = mul nsw i32 %z.0, 100
  %mul45 = mul nsw i32 %mul44, 100
  %add46 = add nsw i32 %add43, %mul45
  %mul47 = mul nsw i32 20, %add46
  %add48 = add nsw i32 4, %mul47
  %idxprom49 = sext i32 %add48 to i64
  %arrayidx50 = getelementptr inbounds double, double* %grid, i64 %idxprom49
  %i5 = load double, double* %arrayidx50, align 8
  %add51 = fadd double %add41, %i5
  %mul52 = mul nsw i32 %y.0, 100
  %add53 = add nsw i32 %x.0, %mul52
  %mul54 = mul nsw i32 %z.0, 100
  %mul55 = mul nsw i32 %mul54, 100
  %add56 = add nsw i32 %add53, %mul55
  %mul57 = mul nsw i32 20, %add56
  %add58 = add nsw i32 5, %mul57
  %idxprom59 = sext i32 %add58 to i64
  %arrayidx60 = getelementptr inbounds double, double* %grid, i64 %idxprom59
  %i6 = load double, double* %arrayidx60, align 8
  %add61 = fadd double %add51, %i6
  %mul62 = mul nsw i32 %y.0, 100
  %add63 = add nsw i32 %x.0, %mul62
  %mul64 = mul nsw i32 %z.0, 100
  %mul65 = mul nsw i32 %mul64, 100
  %add66 = add nsw i32 %add63, %mul65
  %mul67 = mul nsw i32 20, %add66
  %add68 = add nsw i32 6, %mul67
  %idxprom69 = sext i32 %add68 to i64
  %arrayidx70 = getelementptr inbounds double, double* %grid, i64 %idxprom69
  %i7 = load double, double* %arrayidx70, align 8
  %add71 = fadd double %add61, %i7
  %mul72 = mul nsw i32 %y.0, 100
  %add73 = add nsw i32 %x.0, %mul72
  %mul74 = mul nsw i32 %z.0, 100
  %mul75 = mul nsw i32 %mul74, 100
  %add76 = add nsw i32 %add73, %mul75
  %mul77 = mul nsw i32 20, %add76
  %add78 = add nsw i32 7, %mul77
  %idxprom79 = sext i32 %add78 to i64
  %arrayidx80 = getelementptr inbounds double, double* %grid, i64 %idxprom79
  %i8 = load double, double* %arrayidx80, align 8
  %add81 = fadd double %add71, %i8
  %mul82 = mul nsw i32 %y.0, 100
  %add83 = add nsw i32 %x.0, %mul82
  %mul84 = mul nsw i32 %z.0, 100
  %mul85 = mul nsw i32 %mul84, 100
  %add86 = add nsw i32 %add83, %mul85
  %mul87 = mul nsw i32 20, %add86
  %add88 = add nsw i32 8, %mul87
  %idxprom89 = sext i32 %add88 to i64
  %arrayidx90 = getelementptr inbounds double, double* %grid, i64 %idxprom89
  %i9 = load double, double* %arrayidx90, align 8
  %add91 = fadd double %add81, %i9
  %mul92 = mul nsw i32 %y.0, 100
  %add93 = add nsw i32 %x.0, %mul92
  %mul94 = mul nsw i32 %z.0, 100
  %mul95 = mul nsw i32 %mul94, 100
  %add96 = add nsw i32 %add93, %mul95
  %mul97 = mul nsw i32 20, %add96
  %add98 = add nsw i32 9, %mul97
  %idxprom99 = sext i32 %add98 to i64
  %arrayidx100 = getelementptr inbounds double, double* %grid, i64 %idxprom99
  %i10 = load double, double* %arrayidx100, align 8
  %add101 = fadd double %add91, %i10
  %mul102 = mul nsw i32 %y.0, 100
  %add103 = add nsw i32 %x.0, %mul102
  %mul104 = mul nsw i32 %z.0, 100
  %mul105 = mul nsw i32 %mul104, 100
  %add106 = add nsw i32 %add103, %mul105
  %mul107 = mul nsw i32 20, %add106
  %add108 = add nsw i32 10, %mul107
  %idxprom109 = sext i32 %add108 to i64
  %arrayidx110 = getelementptr inbounds double, double* %grid, i64 %idxprom109
  %i11 = load double, double* %arrayidx110, align 8
  %add111 = fadd double %add101, %i11
  %mul112 = mul nsw i32 %y.0, 100
  %add113 = add nsw i32 %x.0, %mul112
  %mul114 = mul nsw i32 %z.0, 100
  %mul115 = mul nsw i32 %mul114, 100
  %add116 = add nsw i32 %add113, %mul115
  %mul117 = mul nsw i32 20, %add116
  %add118 = add nsw i32 11, %mul117
  %idxprom119 = sext i32 %add118 to i64
  %arrayidx120 = getelementptr inbounds double, double* %grid, i64 %idxprom119
  %i12 = load double, double* %arrayidx120, align 8
  %add121 = fadd double %add111, %i12
  %mul122 = mul nsw i32 %y.0, 100
  %add123 = add nsw i32 %x.0, %mul122
  %mul124 = mul nsw i32 %z.0, 100
  %mul125 = mul nsw i32 %mul124, 100
  %add126 = add nsw i32 %add123, %mul125
  %mul127 = mul nsw i32 20, %add126
  %add128 = add nsw i32 12, %mul127
  %idxprom129 = sext i32 %add128 to i64
  %arrayidx130 = getelementptr inbounds double, double* %grid, i64 %idxprom129
  %i13 = load double, double* %arrayidx130, align 8
  %add131 = fadd double %add121, %i13
  %mul132 = mul nsw i32 %y.0, 100
  %add133 = add nsw i32 %x.0, %mul132
  %mul134 = mul nsw i32 %z.0, 100
  %mul135 = mul nsw i32 %mul134, 100
  %add136 = add nsw i32 %add133, %mul135
  %mul137 = mul nsw i32 20, %add136
  %add138 = add nsw i32 13, %mul137
  %idxprom139 = sext i32 %add138 to i64
  %arrayidx140 = getelementptr inbounds double, double* %grid, i64 %idxprom139
  %i14 = load double, double* %arrayidx140, align 8
  %add141 = fadd double %add131, %i14
  %mul142 = mul nsw i32 %y.0, 100
  %add143 = add nsw i32 %x.0, %mul142
  %mul144 = mul nsw i32 %z.0, 100
  %mul145 = mul nsw i32 %mul144, 100
  %add146 = add nsw i32 %add143, %mul145
  %mul147 = mul nsw i32 20, %add146
  %add148 = add nsw i32 14, %mul147
  %idxprom149 = sext i32 %add148 to i64
  %arrayidx150 = getelementptr inbounds double, double* %grid, i64 %idxprom149
  %i15 = load double, double* %arrayidx150, align 8
  %add151 = fadd double %add141, %i15
  %mul152 = mul nsw i32 %y.0, 100
  %add153 = add nsw i32 %x.0, %mul152
  %mul154 = mul nsw i32 %z.0, 100
  %mul155 = mul nsw i32 %mul154, 100
  %add156 = add nsw i32 %add153, %mul155
  %mul157 = mul nsw i32 20, %add156
  %add158 = add nsw i32 15, %mul157
  %idxprom159 = sext i32 %add158 to i64
  %arrayidx160 = getelementptr inbounds double, double* %grid, i64 %idxprom159
  %i16 = load double, double* %arrayidx160, align 8
  %add161 = fadd double %add151, %i16
  %mul162 = mul nsw i32 %y.0, 100
  %add163 = add nsw i32 %x.0, %mul162
  %mul164 = mul nsw i32 %z.0, 100
  %mul165 = mul nsw i32 %mul164, 100
  %add166 = add nsw i32 %add163, %mul165
  %mul167 = mul nsw i32 20, %add166
  %add168 = add nsw i32 16, %mul167
  %idxprom169 = sext i32 %add168 to i64
  %arrayidx170 = getelementptr inbounds double, double* %grid, i64 %idxprom169
  %i17 = load double, double* %arrayidx170, align 8
  %add171 = fadd double %add161, %i17
  %mul172 = mul nsw i32 %y.0, 100
  %add173 = add nsw i32 %x.0, %mul172
  %mul174 = mul nsw i32 %z.0, 100
  %mul175 = mul nsw i32 %mul174, 100
  %add176 = add nsw i32 %add173, %mul175
  %mul177 = mul nsw i32 20, %add176
  %add178 = add nsw i32 17, %mul177
  %idxprom179 = sext i32 %add178 to i64
  %arrayidx180 = getelementptr inbounds double, double* %grid, i64 %idxprom179
  %i18 = load double, double* %arrayidx180, align 8
  %add181 = fadd double %add171, %i18
  %mul182 = mul nsw i32 %y.0, 100
  %add183 = add nsw i32 %x.0, %mul182
  %mul184 = mul nsw i32 %z.0, 100
  %mul185 = mul nsw i32 %mul184, 100
  %add186 = add nsw i32 %add183, %mul185
  %mul187 = mul nsw i32 20, %add186
  %add188 = add nsw i32 18, %mul187
  %idxprom189 = sext i32 %add188 to i64
  %arrayidx190 = getelementptr inbounds double, double* %grid, i64 %idxprom189
  %i19 = load double, double* %arrayidx190, align 8
  %add191 = fadd double %add181, %i19
  %mul192 = mul nsw i32 %y.0, 100
  %add193 = add nsw i32 %x.0, %mul192
  %mul194 = mul nsw i32 %z.0, 100
  %mul195 = mul nsw i32 %mul194, 100
  %add196 = add nsw i32 %add193, %mul195
  %mul197 = mul nsw i32 20, %add196
  %add198 = add nsw i32 3, %mul197
  %idxprom199 = sext i32 %add198 to i64
  %arrayidx200 = getelementptr inbounds double, double* %grid, i64 %idxprom199
  %i20 = load double, double* %arrayidx200, align 8
  %mul201 = mul nsw i32 %y.0, 100
  %add202 = add nsw i32 %x.0, %mul201
  %mul203 = mul nsw i32 %z.0, 100
  %mul204 = mul nsw i32 %mul203, 100
  %add205 = add nsw i32 %add202, %mul204
  %mul206 = mul nsw i32 20, %add205
  %add207 = add nsw i32 4, %mul206
  %idxprom208 = sext i32 %add207 to i64
  %arrayidx209 = getelementptr inbounds double, double* %grid, i64 %idxprom208
  %i21 = load double, double* %arrayidx209, align 8
  %sub = fsub double %i20, %i21
  %mul210 = mul nsw i32 %y.0, 100
  %add211 = add nsw i32 %x.0, %mul210
  %mul212 = mul nsw i32 %z.0, 100
  %mul213 = mul nsw i32 %mul212, 100
  %add214 = add nsw i32 %add211, %mul213
  %mul215 = mul nsw i32 20, %add214
  %add216 = add nsw i32 7, %mul215
  %idxprom217 = sext i32 %add216 to i64
  %arrayidx218 = getelementptr inbounds double, double* %grid, i64 %idxprom217
  %i22 = load double, double* %arrayidx218, align 8
  %add219 = fadd double %sub, %i22
  %mul220 = mul nsw i32 %y.0, 100
  %add221 = add nsw i32 %x.0, %mul220
  %mul222 = mul nsw i32 %z.0, 100
  %mul223 = mul nsw i32 %mul222, 100
  %add224 = add nsw i32 %add221, %mul223
  %mul225 = mul nsw i32 20, %add224
  %add226 = add nsw i32 8, %mul225
  %idxprom227 = sext i32 %add226 to i64
  %arrayidx228 = getelementptr inbounds double, double* %grid, i64 %idxprom227
  %i23 = load double, double* %arrayidx228, align 8
  %sub229 = fsub double %add219, %i23
  %mul230 = mul nsw i32 %y.0, 100
  %add231 = add nsw i32 %x.0, %mul230
  %mul232 = mul nsw i32 %z.0, 100
  %mul233 = mul nsw i32 %mul232, 100
  %add234 = add nsw i32 %add231, %mul233
  %mul235 = mul nsw i32 20, %add234
  %add236 = add nsw i32 9, %mul235
  %idxprom237 = sext i32 %add236 to i64
  %arrayidx238 = getelementptr inbounds double, double* %grid, i64 %idxprom237
  %i24 = load double, double* %arrayidx238, align 8
  %add239 = fadd double %sub229, %i24
  %mul240 = mul nsw i32 %y.0, 100
  %add241 = add nsw i32 %x.0, %mul240
  %mul242 = mul nsw i32 %z.0, 100
  %mul243 = mul nsw i32 %mul242, 100
  %add244 = add nsw i32 %add241, %mul243
  %mul245 = mul nsw i32 20, %add244
  %add246 = add nsw i32 10, %mul245
  %idxprom247 = sext i32 %add246 to i64
  %arrayidx248 = getelementptr inbounds double, double* %grid, i64 %idxprom247
  %i25 = load double, double* %arrayidx248, align 8
  %sub249 = fsub double %add239, %i25
  %mul250 = mul nsw i32 %y.0, 100
  %add251 = add nsw i32 %x.0, %mul250
  %mul252 = mul nsw i32 %z.0, 100
  %mul253 = mul nsw i32 %mul252, 100
  %add254 = add nsw i32 %add251, %mul253
  %mul255 = mul nsw i32 20, %add254
  %add256 = add nsw i32 15, %mul255
  %idxprom257 = sext i32 %add256 to i64
  %arrayidx258 = getelementptr inbounds double, double* %grid, i64 %idxprom257
  %i26 = load double, double* %arrayidx258, align 8
  %add259 = fadd double %sub249, %i26
  %mul260 = mul nsw i32 %y.0, 100
  %add261 = add nsw i32 %x.0, %mul260
  %mul262 = mul nsw i32 %z.0, 100
  %mul263 = mul nsw i32 %mul262, 100
  %add264 = add nsw i32 %add261, %mul263
  %mul265 = mul nsw i32 20, %add264
  %add266 = add nsw i32 16, %mul265
  %idxprom267 = sext i32 %add266 to i64
  %arrayidx268 = getelementptr inbounds double, double* %grid, i64 %idxprom267
  %i27 = load double, double* %arrayidx268, align 8
  %add269 = fadd double %add259, %i27
  %mul270 = mul nsw i32 %y.0, 100
  %add271 = add nsw i32 %x.0, %mul270
  %mul272 = mul nsw i32 %z.0, 100
  %mul273 = mul nsw i32 %mul272, 100
  %add274 = add nsw i32 %add271, %mul273
  %mul275 = mul nsw i32 20, %add274
  %add276 = add nsw i32 17, %mul275
  %idxprom277 = sext i32 %add276 to i64
  %arrayidx278 = getelementptr inbounds double, double* %grid, i64 %idxprom277
  %i28 = load double, double* %arrayidx278, align 8
  %sub279 = fsub double %add269, %i28
  %mul280 = mul nsw i32 %y.0, 100
  %add281 = add nsw i32 %x.0, %mul280
  %mul282 = mul nsw i32 %z.0, 100
  %mul283 = mul nsw i32 %mul282, 100
  %add284 = add nsw i32 %add281, %mul283
  %mul285 = mul nsw i32 20, %add284
  %add286 = add nsw i32 18, %mul285
  %idxprom287 = sext i32 %add286 to i64
  %arrayidx288 = getelementptr inbounds double, double* %grid, i64 %idxprom287
  %i29 = load double, double* %arrayidx288, align 8
  %sub289 = fsub double %sub279, %i29
  %mul290 = mul nsw i32 %y.0, 100
  %add291 = add nsw i32 %x.0, %mul290
  %mul292 = mul nsw i32 %z.0, 100
  %mul293 = mul nsw i32 %mul292, 100
  %add294 = add nsw i32 %add291, %mul293
  %mul295 = mul nsw i32 20, %add294
  %add296 = add nsw i32 1, %mul295
  %idxprom297 = sext i32 %add296 to i64
  %arrayidx298 = getelementptr inbounds double, double* %grid, i64 %idxprom297
  %i30 = load double, double* %arrayidx298, align 8
  %mul299 = mul nsw i32 %y.0, 100
  %add300 = add nsw i32 %x.0, %mul299
  %mul301 = mul nsw i32 %z.0, 100
  %mul302 = mul nsw i32 %mul301, 100
  %add303 = add nsw i32 %add300, %mul302
  %mul304 = mul nsw i32 20, %add303
  %add305 = add nsw i32 2, %mul304
  %idxprom306 = sext i32 %add305 to i64
  %arrayidx307 = getelementptr inbounds double, double* %grid, i64 %idxprom306
  %i31 = load double, double* %arrayidx307, align 8
  %sub308 = fsub double %i30, %i31
  %mul309 = mul nsw i32 %y.0, 100
  %add310 = add nsw i32 %x.0, %mul309
  %mul311 = mul nsw i32 %z.0, 100
  %mul312 = mul nsw i32 %mul311, 100
  %add313 = add nsw i32 %add310, %mul312
  %mul314 = mul nsw i32 20, %add313
  %add315 = add nsw i32 7, %mul314
  %idxprom316 = sext i32 %add315 to i64
  %arrayidx317 = getelementptr inbounds double, double* %grid, i64 %idxprom316
  %i32 = load double, double* %arrayidx317, align 8
  %add318 = fadd double %sub308, %i32
  %mul319 = mul nsw i32 %y.0, 100
  %add320 = add nsw i32 %x.0, %mul319
  %mul321 = mul nsw i32 %z.0, 100
  %mul322 = mul nsw i32 %mul321, 100
  %add323 = add nsw i32 %add320, %mul322
  %mul324 = mul nsw i32 20, %add323
  %add325 = add nsw i32 8, %mul324
  %idxprom326 = sext i32 %add325 to i64
  %arrayidx327 = getelementptr inbounds double, double* %grid, i64 %idxprom326
  %i33 = load double, double* %arrayidx327, align 8
  %add328 = fadd double %add318, %i33
  %mul329 = mul nsw i32 %y.0, 100
  %add330 = add nsw i32 %x.0, %mul329
  %mul331 = mul nsw i32 %z.0, 100
  %mul332 = mul nsw i32 %mul331, 100
  %add333 = add nsw i32 %add330, %mul332
  %mul334 = mul nsw i32 20, %add333
  %add335 = add nsw i32 9, %mul334
  %idxprom336 = sext i32 %add335 to i64
  %arrayidx337 = getelementptr inbounds double, double* %grid, i64 %idxprom336
  %i34 = load double, double* %arrayidx337, align 8
  %sub338 = fsub double %add328, %i34
  %mul339 = mul nsw i32 %y.0, 100
  %add340 = add nsw i32 %x.0, %mul339
  %mul341 = mul nsw i32 %z.0, 100
  %mul342 = mul nsw i32 %mul341, 100
  %add343 = add nsw i32 %add340, %mul342
  %mul344 = mul nsw i32 20, %add343
  %add345 = add nsw i32 10, %mul344
  %idxprom346 = sext i32 %add345 to i64
  %arrayidx347 = getelementptr inbounds double, double* %grid, i64 %idxprom346
  %i35 = load double, double* %arrayidx347, align 8
  %sub348 = fsub double %sub338, %i35
  %mul349 = mul nsw i32 %y.0, 100
  %add350 = add nsw i32 %x.0, %mul349
  %mul351 = mul nsw i32 %z.0, 100
  %mul352 = mul nsw i32 %mul351, 100
  %add353 = add nsw i32 %add350, %mul352
  %mul354 = mul nsw i32 20, %add353
  %add355 = add nsw i32 11, %mul354
  %idxprom356 = sext i32 %add355 to i64
  %arrayidx357 = getelementptr inbounds double, double* %grid, i64 %idxprom356
  %i36 = load double, double* %arrayidx357, align 8
  %add358 = fadd double %sub348, %i36
  %mul359 = mul nsw i32 %y.0, 100
  %add360 = add nsw i32 %x.0, %mul359
  %mul361 = mul nsw i32 %z.0, 100
  %mul362 = mul nsw i32 %mul361, 100
  %add363 = add nsw i32 %add360, %mul362
  %mul364 = mul nsw i32 20, %add363
  %add365 = add nsw i32 12, %mul364
  %idxprom366 = sext i32 %add365 to i64
  %arrayidx367 = getelementptr inbounds double, double* %grid, i64 %idxprom366
  %i37 = load double, double* %arrayidx367, align 8
  %add368 = fadd double %add358, %i37
  %mul369 = mul nsw i32 %y.0, 100
  %add370 = add nsw i32 %x.0, %mul369
  %mul371 = mul nsw i32 %z.0, 100
  %mul372 = mul nsw i32 %mul371, 100
  %add373 = add nsw i32 %add370, %mul372
  %mul374 = mul nsw i32 20, %add373
  %add375 = add nsw i32 13, %mul374
  %idxprom376 = sext i32 %add375 to i64
  %arrayidx377 = getelementptr inbounds double, double* %grid, i64 %idxprom376
  %i38 = load double, double* %arrayidx377, align 8
  %sub378 = fsub double %add368, %i38
  %mul379 = mul nsw i32 %y.0, 100
  %add380 = add nsw i32 %x.0, %mul379
  %mul381 = mul nsw i32 %z.0, 100
  %mul382 = mul nsw i32 %mul381, 100
  %add383 = add nsw i32 %add380, %mul382
  %mul384 = mul nsw i32 20, %add383
  %add385 = add nsw i32 14, %mul384
  %idxprom386 = sext i32 %add385 to i64
  %arrayidx387 = getelementptr inbounds double, double* %grid, i64 %idxprom386
  %i39 = load double, double* %arrayidx387, align 8
  %sub388 = fsub double %sub378, %i39
  %mul389 = mul nsw i32 %y.0, 100
  %add390 = add nsw i32 %x.0, %mul389
  %mul391 = mul nsw i32 %z.0, 100
  %mul392 = mul nsw i32 %mul391, 100
  %add393 = add nsw i32 %add390, %mul392
  %mul394 = mul nsw i32 20, %add393
  %add395 = add nsw i32 5, %mul394
  %idxprom396 = sext i32 %add395 to i64
  %arrayidx397 = getelementptr inbounds double, double* %grid, i64 %idxprom396
  %i40 = load double, double* %arrayidx397, align 8
  %mul398 = mul nsw i32 %y.0, 100
  %add399 = add nsw i32 %x.0, %mul398
  %mul400 = mul nsw i32 %z.0, 100
  %mul401 = mul nsw i32 %mul400, 100
  %add402 = add nsw i32 %add399, %mul401
  %mul403 = mul nsw i32 20, %add402
  %add404 = add nsw i32 6, %mul403
  %idxprom405 = sext i32 %add404 to i64
  %arrayidx406 = getelementptr inbounds double, double* %grid, i64 %idxprom405
  %i41 = load double, double* %arrayidx406, align 8
  %sub407 = fsub double %i40, %i41
  %mul408 = mul nsw i32 %y.0, 100
  %add409 = add nsw i32 %x.0, %mul408
  %mul410 = mul nsw i32 %z.0, 100
  %mul411 = mul nsw i32 %mul410, 100
  %add412 = add nsw i32 %add409, %mul411
  %mul413 = mul nsw i32 20, %add412
  %add414 = add nsw i32 11, %mul413
  %idxprom415 = sext i32 %add414 to i64
  %arrayidx416 = getelementptr inbounds double, double* %grid, i64 %idxprom415
  %i42 = load double, double* %arrayidx416, align 8
  %add417 = fadd double %sub407, %i42
  %mul418 = mul nsw i32 %y.0, 100
  %add419 = add nsw i32 %x.0, %mul418
  %mul420 = mul nsw i32 %z.0, 100
  %mul421 = mul nsw i32 %mul420, 100
  %add422 = add nsw i32 %add419, %mul421
  %mul423 = mul nsw i32 20, %add422
  %add424 = add nsw i32 12, %mul423
  %idxprom425 = sext i32 %add424 to i64
  %arrayidx426 = getelementptr inbounds double, double* %grid, i64 %idxprom425
  %i43 = load double, double* %arrayidx426, align 8
  %sub427 = fsub double %add417, %i43
  %mul428 = mul nsw i32 %y.0, 100
  %add429 = add nsw i32 %x.0, %mul428
  %mul430 = mul nsw i32 %z.0, 100
  %mul431 = mul nsw i32 %mul430, 100
  %add432 = add nsw i32 %add429, %mul431
  %mul433 = mul nsw i32 20, %add432
  %add434 = add nsw i32 13, %mul433
  %idxprom435 = sext i32 %add434 to i64
  %arrayidx436 = getelementptr inbounds double, double* %grid, i64 %idxprom435
  %i44 = load double, double* %arrayidx436, align 8
  %add437 = fadd double %sub427, %i44
  %mul438 = mul nsw i32 %y.0, 100
  %add439 = add nsw i32 %x.0, %mul438
  %mul440 = mul nsw i32 %z.0, 100
  %mul441 = mul nsw i32 %mul440, 100
  %add442 = add nsw i32 %add439, %mul441
  %mul443 = mul nsw i32 20, %add442
  %add444 = add nsw i32 14, %mul443
  %idxprom445 = sext i32 %add444 to i64
  %arrayidx446 = getelementptr inbounds double, double* %grid, i64 %idxprom445
  %i45 = load double, double* %arrayidx446, align 8
  %sub447 = fsub double %add437, %i45
  %mul448 = mul nsw i32 %y.0, 100
  %add449 = add nsw i32 %x.0, %mul448
  %mul450 = mul nsw i32 %z.0, 100
  %mul451 = mul nsw i32 %mul450, 100
  %add452 = add nsw i32 %add449, %mul451
  %mul453 = mul nsw i32 20, %add452
  %add454 = add nsw i32 15, %mul453
  %idxprom455 = sext i32 %add454 to i64
  %arrayidx456 = getelementptr inbounds double, double* %grid, i64 %idxprom455
  %i46 = load double, double* %arrayidx456, align 8
  %add457 = fadd double %sub447, %i46
  %mul458 = mul nsw i32 %y.0, 100
  %add459 = add nsw i32 %x.0, %mul458
  %mul460 = mul nsw i32 %z.0, 100
  %mul461 = mul nsw i32 %mul460, 100
  %add462 = add nsw i32 %add459, %mul461
  %mul463 = mul nsw i32 20, %add462
  %add464 = add nsw i32 16, %mul463
  %idxprom465 = sext i32 %add464 to i64
  %arrayidx466 = getelementptr inbounds double, double* %grid, i64 %idxprom465
  %i47 = load double, double* %arrayidx466, align 8
  %sub467 = fsub double %add457, %i47
  %mul468 = mul nsw i32 %y.0, 100
  %add469 = add nsw i32 %x.0, %mul468
  %mul470 = mul nsw i32 %z.0, 100
  %mul471 = mul nsw i32 %mul470, 100
  %add472 = add nsw i32 %add469, %mul471
  %mul473 = mul nsw i32 20, %add472
  %add474 = add nsw i32 17, %mul473
  %idxprom475 = sext i32 %add474 to i64
  %arrayidx476 = getelementptr inbounds double, double* %grid, i64 %idxprom475
  %i48 = load double, double* %arrayidx476, align 8
  %add477 = fadd double %sub467, %i48
  %mul478 = mul nsw i32 %y.0, 100
  %add479 = add nsw i32 %x.0, %mul478
  %mul480 = mul nsw i32 %z.0, 100
  %mul481 = mul nsw i32 %mul480, 100
  %add482 = add nsw i32 %add479, %mul481
  %mul483 = mul nsw i32 20, %add482
  %add484 = add nsw i32 18, %mul483
  %idxprom485 = sext i32 %add484 to i64
  %arrayidx486 = getelementptr inbounds double, double* %grid, i64 %idxprom485
  %i49 = load double, double* %arrayidx486, align 8
  %sub487 = fsub double %add477, %i49
  %div = fdiv double %sub289, %add191
  %div488 = fdiv double %sub388, %add191
  %div489 = fdiv double %sub487, %add191
  %tobool490 = icmp ne i32 %binary, 0
  br i1 %tobool490, label %if.then, label %if.else

if.then:                                          ; preds = %for.body6
  call void @loadValue(%struct._IO_FILE* %call, float* %fileUx)
  call void @loadValue(%struct._IO_FILE* %call, float* %fileUy)
  call void @loadValue(%struct._IO_FILE* %call, float* %fileUz)
  br label %if.end

if.else:                                          ; preds = %for.body6
  %call491 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %call, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.7, i64 0, i64 0), float* %fileUx, float* %fileUy, float* %fileUz)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %i50 = load float, float* %fileUx, align 4
  %conv = fpext float %i50 to double
  %sub492 = fsub double %div, %conv
  %conv493 = fptrunc double %sub492 to float
  %i51 = load float, float* %fileUy, align 4
  %conv494 = fpext float %i51 to double
  %sub495 = fsub double %div488, %conv494
  %conv496 = fptrunc double %sub495 to float
  %i52 = load float, float* %fileUz, align 4
  %conv497 = fpext float %i52 to double
  %sub498 = fsub double %div489, %conv497
  %conv499 = fptrunc double %sub498 to float
  %mul500 = fmul float %conv493, %conv493
  %mul501 = fmul float %conv496, %conv496
  %add502 = fadd float %mul500, %mul501
  %mul503 = fmul float %conv499, %conv499
  %add504 = fadd float %add502, %mul503
  %cmp505 = fcmp ogt float %add504, %maxDiff2.2
  br i1 %cmp505, label %if.then507, label %if.end508

if.then507:                                       ; preds = %if.end
  br label %if.end508

if.end508:                                        ; preds = %if.then507, %if.end
  %maxDiff2.3 = phi float [ %add504, %if.then507 ], [ %maxDiff2.2, %if.end ]
  br label %for.inc

for.inc:                                          ; preds = %if.end508
  %inc = add nsw i32 %x.0, 1
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  br label %for.inc509

for.inc509:                                       ; preds = %for.end
  %inc510 = add nsw i32 %y.0, 1
  br label %for.cond1

for.end511:                                       ; preds = %for.cond1
  br label %for.inc512

for.inc512:                                       ; preds = %for.end511
  %inc513 = add nsw i32 %z.0, 1
  br label %for.cond

for.end514:                                       ; preds = %for.cond
  %conv515 = fpext float %maxDiff2.0 to double
  %call516 = call double @sqrt(double %conv515) #6
  %call517 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.8, i64 0, i64 0), double %call516)
  %call518 = call i32 @fclose(%struct._IO_FILE* %call)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal void @loadValue(%struct._IO_FILE* %file, float* %v) #0 {
entry:
  %litteBigEndianTest = alloca i32, align 4
  %buffer = alloca [4 x i8], align 1
  store i32 1, i32* %litteBigEndianTest, align 4
  %i = bitcast i32* %litteBigEndianTest to i8*
  %i1 = load i8, i8* %i, align 4
  %conv = zext i8 %i1 to i32
  %cmp = icmp eq i32 %conv, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i2 = bitcast float* %v to i8*
  %arraydecay = getelementptr inbounds [4 x i8], [4 x i8]* %buffer, i64 0, i64 0
  %call = call i64 @fread(i8* %arraydecay, i64 4, i64 1, %struct._IO_FILE* %file)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.then
  %i.0 = phi i32 [ 0, %if.then ], [ %inc, %for.inc ]
  %conv2 = sext i32 %i.0 to i64
  %cmp3 = icmp ult i64 %conv2, 4
  br i1 %cmp3, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %conv5 = sext i32 %i.0 to i64
  %sub = sub i64 4, %conv5
  %sub6 = sub i64 %sub, 1
  %arrayidx = getelementptr inbounds [4 x i8], [4 x i8]* %buffer, i64 0, i64 %sub6
  %i3 = load i8, i8* %arrayidx, align 1
  %idxprom = sext i32 %i.0 to i64
  %arrayidx7 = getelementptr inbounds i8, i8* %i2, i64 %idxprom
  store i8 %i3, i8* %arrayidx7, align 1
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %if.end

if.else:                                          ; preds = %entry
  %i4 = bitcast float* %v to i8*
  %call8 = call i64 @fread(i8* %i4, i64 4, i64 1, %struct._IO_FILE* %file)
  br label %if.end

if.end:                                           ; preds = %if.else, %for.end
  ret void
}

declare dso_local i32 @__isoc99_fscanf(%struct._IO_FILE*, i8*, ...) #2

declare dso_local i64 @fread(i8*, i64, i64, %struct._IO_FILE*) #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main(i32 %nArgs, i8** %arg) #0 {
entry:
  %param = alloca %struct.MAIN_Param, align 8
  call void @MAIN_parseCommandLine(i32 %nArgs, i8** %arg, %struct.MAIN_Param* %param)
  call void @MAIN_printInfo(%struct.MAIN_Param* %param)
  call void @MAIN_initialize(%struct.MAIN_Param* %param)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %t.0 = phi i32 [ 1, %entry ], [ %inc, %for.inc ]
  %nTimeSteps = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 0
  %i = load i32, i32* %nTimeSteps, align 8
  %cmp = icmp sle i32 %t.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %simType = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 3
  %i1 = load i32, i32* %simType, align 4
  %cmp1 = icmp eq i32 %i1, 1
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  %i2 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay = getelementptr inbounds [26000000 x double], [26000000 x double]* %i2, i64 0, i64 0
  call void @LBM_handleInOutFlow(double* %arraydecay)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %i3 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay2 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i3, i64 0, i64 0
  %i4 = load [26000000 x double]*, [26000000 x double]** @dstGrid, align 8
  %arraydecay3 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i4, i64 0, i64 0
  call void @LBM_performStreamCollide(double* %arraydecay2, double* %arraydecay3)
  call void @LBM_swapGrids([26000000 x double]** @srcGrid, [26000000 x double]** @dstGrid)
  %and = and i32 %t.0, 63
  %cmp4 = icmp eq i32 %and, 0
  br i1 %cmp4, label %if.then5, label %if.end7

if.then5:                                         ; preds = %if.end
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.9, i64 0, i64 0), i32 %t.0)
  %i5 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay6 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i5, i64 0, i64 0
  call void @LBM_showGridStatistics(double* %arraydecay6)
  br label %if.end7

if.end7:                                          ; preds = %if.then5, %if.end
  br label %for.inc

for.inc:                                          ; preds = %if.end7
  %inc = add nsw i32 %t.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @MAIN_finalize(%struct.MAIN_Param* %param)
  ret i32 0
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @MAIN_parseCommandLine(i32 %nArgs, i8** %arg, %struct.MAIN_Param* %param) #0 {
entry:
  %fileStat = alloca %struct.stat, align 8
  %cmp = icmp slt i32 %nArgs, 5
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %cmp1 = icmp sgt i32 %nArgs, 6
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([109 x i8], [109 x i8]* @.str.1.12, i64 0, i64 0))
  call void @exit(i32 1) #7
  unreachable

if.end:                                           ; preds = %lor.lhs.false
  %arrayidx = getelementptr inbounds i8*, i8** %arg, i64 1
  %i = load i8*, i8** %arrayidx, align 8
  %call2 = call i32 @atoi(i8* %i) #8
  %nTimeSteps = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 0
  store i32 %call2, i32* %nTimeSteps, align 8
  %arrayidx3 = getelementptr inbounds i8*, i8** %arg, i64 2
  %i1 = load i8*, i8** %arrayidx3, align 8
  %resultFilename = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 1
  store i8* %i1, i8** %resultFilename, align 8
  %arrayidx4 = getelementptr inbounds i8*, i8** %arg, i64 3
  %i2 = load i8*, i8** %arrayidx4, align 8
  %call5 = call i32 @atoi(i8* %i2) #8
  %action = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 2
  store i32 %call5, i32* %action, align 8
  %arrayidx6 = getelementptr inbounds i8*, i8** %arg, i64 4
  %i3 = load i8*, i8** %arrayidx6, align 8
  %call7 = call i32 @atoi(i8* %i3) #8
  %simType = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 3
  store i32 %call7, i32* %simType, align 4
  %cmp8 = icmp eq i32 %nArgs, 6
  br i1 %cmp8, label %if.then9, label %if.else

if.then9:                                         ; preds = %if.end
  %arrayidx10 = getelementptr inbounds i8*, i8** %arg, i64 5
  %i4 = load i8*, i8** %arrayidx10, align 8
  %obstacleFilename = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  store i8* %i4, i8** %obstacleFilename, align 8
  %obstacleFilename11 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i5 = load i8*, i8** %obstacleFilename11, align 8
  %call12 = call i32 @stat(i8* %i5, %struct.stat* %fileStat) #6
  %cmp13 = icmp ne i32 %call12, 0
  br i1 %cmp13, label %if.then14, label %if.end17

if.then14:                                        ; preds = %if.then9
  %obstacleFilename15 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i6 = load i8*, i8** %obstacleFilename15, align 8
  %call16 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([55 x i8], [55 x i8]* @.str.2.13, i64 0, i64 0), i8* %i6)
  call void @exit(i32 1) #7
  unreachable

if.end17:                                         ; preds = %if.then9
  %st_size = getelementptr inbounds %struct.stat, %struct.stat* %fileStat, i32 0, i32 8
  %i7 = load i64, i64* %st_size, align 8
  %cmp18 = icmp ne i64 %i7, 1313130
  br i1 %cmp18, label %if.then19, label %if.end23

if.then19:                                        ; preds = %if.end17
  %obstacleFilename20 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i8 = load i8*, i8** %obstacleFilename20, align 8
  %st_size21 = getelementptr inbounds %struct.stat, %struct.stat* %fileStat, i32 0, i32 8
  %i9 = load i64, i64* %st_size21, align 8
  %conv = trunc i64 %i9 to i32
  %call22 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.3.14, i64 0, i64 0), i8* %i8, i32 %conv, i32 1313130)
  call void @exit(i32 1) #7
  unreachable

if.end23:                                         ; preds = %if.end17
  br label %if.end25

if.else:                                          ; preds = %if.end
  %obstacleFilename24 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  store i8* null, i8** %obstacleFilename24, align 8
  br label %if.end25

if.end25:                                         ; preds = %if.else, %if.end23
  %action26 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 2
  %i10 = load i32, i32* %action26, align 8
  %cmp27 = icmp eq i32 %i10, 1
  br i1 %cmp27, label %land.lhs.true, label %if.end36

land.lhs.true:                                    ; preds = %if.end25
  %resultFilename29 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 1
  %i11 = load i8*, i8** %resultFilename29, align 8
  %call30 = call i32 @stat(i8* %i11, %struct.stat* %fileStat) #6
  %cmp31 = icmp ne i32 %call30, 0
  br i1 %cmp31, label %if.then33, label %if.end36

if.then33:                                        ; preds = %land.lhs.true
  %resultFilename34 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 1
  %i12 = load i8*, i8** %resultFilename34, align 8
  %call35 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @.str.4.15, i64 0, i64 0), i8* %i12)
  call void @exit(i32 1) #7
  unreachable

if.end36:                                         ; preds = %land.lhs.true, %if.end25
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @MAIN_printInfo(%struct.MAIN_Param* %param) #0 {
entry:
  %actionString = alloca [3 x [32 x i8]], align 16
  %simTypeString = alloca [3 x [32 x i8]], align 16
  %i = bitcast [3 x [32 x i8]]* %actionString to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 16 %i, i8* align 16 getelementptr inbounds ([3 x [32 x i8]], [3 x [32 x i8]]* @__const.MAIN_printInfo.actionString, i32 0, i32 0, i32 0), i64 96, i1 false)
  %i1 = bitcast [3 x [32 x i8]]* %simTypeString to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 16 %i1, i8* align 16 getelementptr inbounds ([3 x [32 x i8]], [3 x [32 x i8]]* @__const.MAIN_printInfo.simTypeString, i32 0, i32 0, i32 0), i64 96, i1 false)
  %nTimeSteps = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 0
  %i2 = load i32, i32* %nTimeSteps, align 8
  %resultFilename = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 1
  %i3 = load i8*, i8** %resultFilename, align 8
  %action = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 2
  %i4 = load i32, i32* %action, align 8
  %idxprom = zext i32 %i4 to i64
  %arrayidx = getelementptr inbounds [3 x [32 x i8]], [3 x [32 x i8]]* %actionString, i64 0, i64 %idxprom
  %arraydecay = getelementptr inbounds [32 x i8], [32 x i8]* %arrayidx, i64 0, i64 0
  %simType = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 3
  %i5 = load i32, i32* %simType, align 4
  %idxprom1 = zext i32 %i5 to i64
  %arrayidx2 = getelementptr inbounds [3 x [32 x i8]], [3 x [32 x i8]]* %simTypeString, i64 0, i64 %idxprom1
  %arraydecay3 = getelementptr inbounds [32 x i8], [32 x i8]* %arrayidx2, i64 0, i64 0
  %obstacleFilename = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i6 = load i8*, i8** %obstacleFilename, align 8
  %cmp = icmp eq i8* %i6, null
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  br label %cond.end

cond.false:                                       ; preds = %entry
  %obstacleFilename4 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i7 = load i8*, i8** %obstacleFilename4, align 8
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i8* [ getelementptr inbounds ([7 x i8], [7 x i8]* @.str.6.10, i64 0, i64 0), %cond.true ], [ %i7, %cond.false ]
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([174 x i8], [174 x i8]* @.str.5.11, i64 0, i64 0), i32 100, i32 100, i32 130, double 0x3FF4CCCCCCCCCCCC, i32 %i2, i8* %i3, i8* %arraydecay, i8* %arraydecay3, i8* %cond)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @MAIN_initialize(%struct.MAIN_Param* %param) #0 {
entry:
  call void @LBM_allocateGrid(double** bitcast ([26000000 x double]** @srcGrid to double**))
  call void @LBM_allocateGrid(double** bitcast ([26000000 x double]** @dstGrid to double**))
  %i = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay = getelementptr inbounds [26000000 x double], [26000000 x double]* %i, i64 0, i64 0
  call void @LBM_initializeGrid(double* %arraydecay)
  %i1 = load [26000000 x double]*, [26000000 x double]** @dstGrid, align 8
  %arraydecay1 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i1, i64 0, i64 0
  call void @LBM_initializeGrid(double* %arraydecay1)
  %obstacleFilename = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i2 = load i8*, i8** %obstacleFilename, align 8
  %cmp = icmp ne i8* %i2, null
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i3 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay2 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i3, i64 0, i64 0
  %obstacleFilename3 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i4 = load i8*, i8** %obstacleFilename3, align 8
  call void @LBM_loadObstacleFile(double* %arraydecay2, i8* %i4)
  %i5 = load [26000000 x double]*, [26000000 x double]** @dstGrid, align 8
  %arraydecay4 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i5, i64 0, i64 0
  %obstacleFilename5 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 4
  %i6 = load i8*, i8** %obstacleFilename5, align 8
  call void @LBM_loadObstacleFile(double* %arraydecay4, i8* %i6)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %simType = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 3
  %i7 = load i32, i32* %simType, align 4
  %cmp6 = icmp eq i32 %i7, 1
  br i1 %cmp6, label %if.then7, label %if.else

if.then7:                                         ; preds = %if.end
  %i8 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay8 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i8, i64 0, i64 0
  call void @LBM_initializeSpecialCellsForChannel(double* %arraydecay8)
  %i9 = load [26000000 x double]*, [26000000 x double]** @dstGrid, align 8
  %arraydecay9 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i9, i64 0, i64 0
  call void @LBM_initializeSpecialCellsForChannel(double* %arraydecay9)
  br label %if.end12

if.else:                                          ; preds = %if.end
  %i10 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay10 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i10, i64 0, i64 0
  call void @LBM_initializeSpecialCellsForLDC(double* %arraydecay10)
  %i11 = load [26000000 x double]*, [26000000 x double]** @dstGrid, align 8
  %arraydecay11 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i11, i64 0, i64 0
  call void @LBM_initializeSpecialCellsForLDC(double* %arraydecay11)
  br label %if.end12

if.end12:                                         ; preds = %if.else, %if.then7
  %i12 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay13 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i12, i64 0, i64 0
  call void @LBM_showGridStatistics(double* %arraydecay13)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @MAIN_finalize(%struct.MAIN_Param* %param) #0 {
entry:
  %i = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay = getelementptr inbounds [26000000 x double], [26000000 x double]* %i, i64 0, i64 0
  call void @LBM_showGridStatistics(double* %arraydecay)
  %action = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 2
  %i1 = load i32, i32* %action, align 8
  %cmp = icmp eq i32 %i1, 1
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i2 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay1 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i2, i64 0, i64 0
  %resultFilename = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 1
  %i3 = load i8*, i8** %resultFilename, align 8
  call void @LBM_compareVelocityField(double* %arraydecay1, i8* %i3, i32 -1)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %action2 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 2
  %i4 = load i32, i32* %action2, align 8
  %cmp3 = icmp eq i32 %i4, 2
  br i1 %cmp3, label %if.then4, label %if.end7

if.then4:                                         ; preds = %if.end
  %i5 = load [26000000 x double]*, [26000000 x double]** @srcGrid, align 8
  %arraydecay5 = getelementptr inbounds [26000000 x double], [26000000 x double]* %i5, i64 0, i64 0
  %resultFilename6 = getelementptr inbounds %struct.MAIN_Param, %struct.MAIN_Param* %param, i32 0, i32 1
  %i6 = load i8*, i8** %resultFilename6, align 8
  call void @LBM_storeVelocityField(double* %arraydecay5, i8* %i6, i32 -1)
  br label %if.end7

if.end7:                                          ; preds = %if.then4, %if.end
  call void @LBM_freeGrid(double** bitcast ([26000000 x double]** @srcGrid to double**))
  call void @LBM_freeGrid(double** bitcast ([26000000 x double]** @dstGrid to double**))
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #4

; Function Attrs: nounwind readonly willreturn
declare dso_local i32 @atoi(i8*) #5

; Function Attrs: nounwind
declare dso_local i32 @stat(i8*, %struct.stat*) #1

attributes #0 = { noinline nounwind uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { argmemonly nofree nosync nounwind willreturn }
attributes #5 = { nounwind readonly willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind }
attributes #7 = { noreturn nounwind }
attributes #8 = { nounwind readonly willreturn }

!llvm.ident = !{!0, !0}
!llvm.module.flags = !{!1}

!0 = !{!"Ubuntu clang version 12.0.1-8build1"}
!1 = !{i32 1, !"wchar_size", i32 4}
