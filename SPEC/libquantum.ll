; ModuleID = 'libquantum.ll'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque
%struct.quantum_reg_struct = type { i32, i32, i32, %struct.quantum_reg_node_struct*, i32* }
%struct.quantum_reg_node_struct = type { { float, float }, i64 }
%struct.__va_list_tag = type { i32, i32, i8*, i8* }
%struct.quantum_matrix_struct = type { i32, i32, { float, float }* }

@status = dso_local global i32 0, align 4
@lambda = dso_local global float 0.000000e+00, align 4
@.str = private unnamed_addr constant [48 x i8] c"Not enough memory for %i-sized array of float!\0A\00", align 1
@.str.1 = private unnamed_addr constant [40 x i8] c"Error allocating %i-element int array!\0A\00", align 1
@.str.1.4 = private unnamed_addr constant [29 x i8] c"Matrix is not a 2x2 matrix!\0A\00", align 1
@.str.2 = private unnamed_addr constant [39 x i8] c"Not enough memory for %i-sized qubit!\0A\00", align 1
@.str.3 = private unnamed_addr constant [39 x i8] c"Not enough memory for %i bytes array!\0A\00", align 1
@.str.4 = private unnamed_addr constant [29 x i8] c"Matrix is not a 4x4 matrix!\0A\00", align 1
@quantum_gate_counter.counter = internal global i32 0, align 4
@quantum_memman.mem = internal global i64 0, align 8
@quantum_memman.max = internal global i64 0, align 8
@.str.14 = private unnamed_addr constant [35 x i8] c"Not enogh memory for %ix%i-Matrix!\00", align 1
@.str.1.19 = private unnamed_addr constant [10 x i8] c"% f %+fi\09\00", align 1
@.str.2.20 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@.str.26 = private unnamed_addr constant [39 x i8] c"Not enough memory for %i-sized qubit!\0A\00", align 1
@opstatus = dso_local global i32 0, align 4
@objcode = dso_local global i8* null, align 8
@position = dso_local global i64 0, align 8
@allocated = dso_local global i64 0, align 8
@globalfile = dso_local global i8* null, align 8
@.str.27 = private unnamed_addr constant [43 x i8] c"Error allocating memory for objcode data!\0A\00", align 1
@.str.1.30 = private unnamed_addr constant [24 x i8] c"Unknown opcode 0x(%X)!\0A\00", align 1
@.str.2.31 = private unnamed_addr constant [45 x i8] c"Error reallocating memory for objcode data!\0A\00", align 1
@stderr = external dso_local global %struct._IO_FILE*, align 8
@.str.3.32 = private unnamed_addr constant [74 x i8] c"Object code generation not active! Forgot to call quantum_objcode_start?\0A\00", align 1
@.str.4.33 = private unnamed_addr constant [2 x i8] c"w\00", align 1
@.str.5 = private unnamed_addr constant [2 x i8] c"r\00", align 1
@.str.6 = private unnamed_addr constant [41 x i8] c"quantum_objcode_run: Could not open %s: \00", align 1
@.str.7 = private unnamed_addr constant [28 x i8] c"%i: Unknown opcode 0x(%X)!\0A\00", align 1
@type = dso_local global i32 0, align 4
@width = dso_local global i32 0, align 4
@quantum_qec_counter.counter = internal global i32 0, align 4
@quantum_qec_counter.freq = internal global i32 1073741824, align 4
@.str.44 = private unnamed_addr constant [51 x i8] c"Error! Cannot convert a multi-column-matrix (%i)!\0A\00", align 1
@.str.1.45 = private unnamed_addr constant [39 x i8] c"Not enough memory for %i-sized qubit!\0A\00", align 1
@.str.2.46 = private unnamed_addr constant [38 x i8] c"Not enough memory for %i-sized hash!\0A\00", align 1
@.str.3.49 = private unnamed_addr constant [9 x i8] c"QUOBFILE\00", align 1
@.str.4.55 = private unnamed_addr constant [23 x i8] c"% f %+fi|%lli> (%e) (|\00", align 1
@.str.5.56 = private unnamed_addr constant [2 x i8] c" \00", align 1
@.str.6.57 = private unnamed_addr constant [3 x i8] c"%i\00", align 1
@.str.7.58 = private unnamed_addr constant [4 x i8] c">)\0A\00", align 1
@.str.8 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@.str.9 = private unnamed_addr constant [10 x i8] c"%i: %lli\0A\00", align 1
@.str.10 = private unnamed_addr constant [13 x i8] c"%i: %i %llu\0A\00", align 1
@.str.11 = private unnamed_addr constant [50 x i8] c"Not enough memory for %i-sized quantum register!\0A\00", align 1
@.str.64 = private unnamed_addr constant [23 x i8] c"Usage: shor [number]\0A\0A\00", align 1
@.str.1.65 = private unnamed_addr constant [17 x i8] c"Invalid number\0A\0A\00", align 1
@.str.2.66 = private unnamed_addr constant [28 x i8] c"N = %i, %i qubits required\0A\00", align 1
@.str.3.67 = private unnamed_addr constant [17 x i8] c"Random seed: %i\0A\00", align 1
@.str.4.68 = private unnamed_addr constant [25 x i8] c"Impossible Measurement!\0A\00", align 1
@.str.5.69 = private unnamed_addr constant [27 x i8] c"Measured zero, try again.\0A\00", align 1
@.str.6.70 = private unnamed_addr constant [19 x i8] c"Measured %i (%f), \00", align 1
@.str.7.71 = private unnamed_addr constant [36 x i8] c"fractional approximation is %i/%i.\0A\00", align 1
@.str.8.72 = private unnamed_addr constant [41 x i8] c"Odd denominator, trying to expand by 2.\0A\00", align 1
@.str.9.73 = private unnamed_addr constant [24 x i8] c"Odd period, try again.\0A\00", align 1
@.str.10.74 = private unnamed_addr constant [24 x i8] c"Possible period is %i.\0A\00", align 1
@.str.11.75 = private unnamed_addr constant [14 x i8] c"%i = %i * %i\0A\00", align 1
@.str.12 = private unnamed_addr constant [41 x i8] c"Unable to determine factors, try again.\0A\00", align 1
@.str.76 = private unnamed_addr constant [6 x i8] c"0.2.4\00", align 1
@seedi = internal global i32 0, align 4

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_ipow(i32 %a, i32 %b) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %r.0 = phi i32 [ 1, %entry ], [ %mul, %for.inc ]
  %cmp = icmp slt i32 %i.0, %b
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %mul = mul nsw i32 %r.0, %a
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i32 %r.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_gcd(i32 %u, i32 %v) #0 {
entry:
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %v.addr.0 = phi i32 [ %v, %entry ], [ %rem, %while.body ]
  %u.addr.0 = phi i32 [ %u, %entry ], [ %v.addr.0, %while.body ]
  %tobool = icmp ne i32 %v.addr.0, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %rem = srem i32 %u.addr.0, %v.addr.0
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret i32 %u.addr.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_frac_approx(i32* %a, i32* %b, i32 %width) #0 {
entry:
  %i = load i32, i32* %a, align 4
  %conv = sitofp i32 %i to float
  %i1 = load i32, i32* %b, align 4
  %conv1 = sitofp i32 %i1 to float
  %div = fdiv float %conv, %conv1
  br label %do.body

do.body:                                          ; preds = %do.cond, %entry
  %num2.0 = phi i32 [ 0, %entry ], [ %num1.0, %do.cond ]
  %den2.0 = phi i32 [ 1, %entry ], [ %den1.0, %do.cond ]
  %g.0 = phi float [ %div, %entry ], [ %conv10, %do.cond ]
  %num1.0 = phi i32 [ 1, %entry ], [ %add14, %do.cond ]
  %den1.0 = phi i32 [ 0, %entry ], [ %add16, %do.cond ]
  %num.0 = phi i32 [ 0, %entry ], [ %add14, %do.cond ]
  %den.0 = phi i32 [ 0, %entry ], [ %add16, %do.cond ]
  %conv2 = fpext float %g.0 to double
  %add = fadd double %conv2, 5.000000e-06
  %conv3 = fptosi double %add to i32
  %conv4 = sitofp i32 %conv3 to double
  %sub = fsub double %conv4, 5.000000e-06
  %conv5 = fpext float %g.0 to double
  %sub6 = fsub double %conv5, %sub
  %conv7 = fptrunc double %sub6 to float
  %conv8 = fpext float %conv7 to double
  %div9 = fdiv double 1.000000e+00, %conv8
  %conv10 = fptrunc double %div9 to float
  %mul = mul nsw i32 %conv3, %den1.0
  %add11 = add nsw i32 %mul, %den2.0
  %shl = shl i32 1, %width
  %cmp = icmp sgt i32 %add11, %shl
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %do.body
  br label %do.end

if.end:                                           ; preds = %do.body
  %mul13 = mul nsw i32 %conv3, %num1.0
  %add14 = add nsw i32 %mul13, %num2.0
  %mul15 = mul nsw i32 %conv3, %den1.0
  %add16 = add nsw i32 %mul15, %den2.0
  br label %do.cond

do.cond:                                          ; preds = %if.end
  %conv17 = sitofp i32 %add14 to float
  %conv18 = sitofp i32 %add16 to float
  %div19 = fdiv float %conv17, %conv18
  %sub20 = fsub float %div19, %div
  %i2 = call float @llvm.fabs.f32(float %sub20)
  %conv21 = fpext float %i2 to double
  %shl22 = shl i32 1, %width
  %mul23 = mul nsw i32 2, %shl22
  %conv24 = sitofp i32 %mul23 to double
  %div25 = fdiv double 1.000000e+00, %conv24
  %cmp26 = fcmp ogt double %conv21, %div25
  br i1 %cmp26, label %do.body, label %do.end

do.end:                                           ; preds = %do.cond, %if.then
  %num.1 = phi i32 [ %num.0, %if.then ], [ %add14, %do.cond ]
  %den.1 = phi i32 [ %den.0, %if.then ], [ %add16, %do.cond ]
  store i32 %num.1, i32* %a, align 4
  store i32 %den.1, i32* %b, align 4
  ret void
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare float @llvm.fabs.f32(float) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_getwidth(i32 %n) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 1, %entry ], [ %inc, %for.inc ]
  %shl = shl i32 1, %i.0
  %cmp = icmp slt i32 %shl, %n
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i32 %i.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_inverse_mod(i32 %n, i32 %c) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 1, %entry ], [ %inc, %for.inc ]
  %mul = mul nsw i32 %i.0, %c
  %rem = srem i32 %mul, %n
  %cmp = icmp ne i32 %rem, 1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i32 %i.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local <2 x float> @quantum_conj(<2 x float> %a.coerce) #2 {
entry:
  %retval = alloca { float, float }, align 4
  %a = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce5 = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %a.realp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real = load float, float* %a.realp, align 4
  %a.imagp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag = load float, float* %a.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %a.real, float* %coerce.realp, align 4
  store float %a.imag, float* %coerce.imagp, align 4
  %i1 = bitcast { float, float }* %coerce to <2 x float>*
  %i2 = load <2 x float>, <2 x float>* %i1, align 4
  %call = call float @quantum_real(<2 x float> %i2)
  %a.realp1 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real2 = load float, float* %a.realp1, align 4
  %a.imagp3 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag4 = load float, float* %a.imagp3, align 4
  %coerce5.realp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 0
  %coerce5.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 1
  store float %a.real2, float* %coerce5.realp, align 4
  store float %a.imag4, float* %coerce5.imagp, align 4
  %i3 = bitcast { float, float }* %coerce5 to <2 x float>*
  %i4 = load <2 x float>, <2 x float>* %i3, align 4
  %call6 = call float @quantum_imag(<2 x float> %i4)
  %mul.rl = fmul float 0.000000e+00, %call6
  %mul.il = fmul float 1.000000e+00, %call6
  %sub.r = fsub float %call, %mul.rl
  %sub.i = fneg float %mul.il
  %retval.realp = getelementptr inbounds { float, float }, { float, float }* %retval, i32 0, i32 0
  %retval.imagp = getelementptr inbounds { float, float }, { float, float }* %retval, i32 0, i32 1
  store float %sub.r, float* %retval.realp, align 4
  store float %sub.i, float* %retval.imagp, align 4
  %i5 = bitcast { float, float }* %retval to <2 x float>*
  %i6 = load <2 x float>, <2 x float>* %i5, align 4
  ret <2 x float> %i6
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_real(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 0
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_imag(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 1
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define dso_local float @quantum_prob(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %a.realp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real = load float, float* %a.realp, align 4
  %a.imagp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag = load float, float* %a.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %a.real, float* %coerce.realp, align 4
  store float %a.imag, float* %coerce.imagp, align 4
  %i1 = bitcast { float, float }* %coerce to <2 x float>*
  %i2 = load <2 x float>, <2 x float>* %i1, align 4
  %call = call float @quantum_prob_inline(<2 x float> %i2)
  ret float %call
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_prob_inline(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce5 = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %a.realp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real = load float, float* %a.realp, align 4
  %a.imagp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag = load float, float* %a.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %a.real, float* %coerce.realp, align 4
  store float %a.imag, float* %coerce.imagp, align 4
  %i1 = bitcast { float, float }* %coerce to <2 x float>*
  %i2 = load <2 x float>, <2 x float>* %i1, align 4
  %call = call float @quantum_real(<2 x float> %i2)
  %a.realp1 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real2 = load float, float* %a.realp1, align 4
  %a.imagp3 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag4 = load float, float* %a.imagp3, align 4
  %coerce5.realp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 0
  %coerce5.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 1
  store float %a.real2, float* %coerce5.realp, align 4
  store float %a.imag4, float* %coerce5.imagp, align 4
  %i3 = bitcast { float, float }* %coerce5 to <2 x float>*
  %i4 = load <2 x float>, <2 x float>* %i3, align 4
  %call6 = call float @quantum_imag(<2 x float> %i4)
  %mul = fmul float %call, %call
  %mul7 = fmul float %call6, %call6
  %add = fadd float %mul, %mul7
  ret float %add
}

; Function Attrs: noinline nounwind uwtable
define dso_local <2 x float> @quantum_cexp(float %phi) #2 {
entry:
  %retval = alloca { float, float }, align 4
  %conv = fpext float %phi to double
  %call = call double @cos(double %conv) #9
  %conv1 = fpext float %phi to double
  %call2 = call double @sin(double %conv1) #9
  %mul.rl = fmul double 0.000000e+00, %call2
  %mul.il = fmul double 1.000000e+00, %call2
  %add.r = fadd double %call, %mul.rl
  %conv3 = fptrunc double %add.r to float
  %conv4 = fptrunc double %mul.il to float
  %retval.realp = getelementptr inbounds { float, float }, { float, float }* %retval, i32 0, i32 0
  %retval.imagp = getelementptr inbounds { float, float }, { float, float }* %retval, i32 0, i32 1
  store float %conv3, float* %retval.realp, align 4
  store float %conv4, float* %retval.imagp, align 4
  %i = bitcast { float, float }* %retval to <2 x float>*
  %i1 = load <2 x float>, <2 x float>* %i, align 4
  ret <2 x float> %i1
}

; Function Attrs: nounwind
declare dso_local double @cos(double) #3

; Function Attrs: nounwind
declare dso_local double @sin(double) #3

; Function Attrs: noinline nounwind uwtable
define dso_local float @quantum_get_decoherence() #0 {
entry:
  %i = load float, float* @lambda, align 4
  ret float %i
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_set_decoherence(float %l) #0 {
entry:
  %tobool = fcmp une float %l, 0.000000e+00
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  store i32 1, i32* @status, align 4
  store float %l, float* @lambda, align 4
  br label %if.end

if.else:                                          ; preds = %entry
  store i32 0, i32* @status, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_decohere(%struct.quantum_reg_struct* %reg) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %coerce66 = alloca { float, float }, align 4
  %call = call i32 @quantum_gate_counter(i32 1)
  %i = load i32, i32* @status, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.then, label %if.end77

if.then:                                          ; preds = %entry
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i1 = load i32, i32* %width, align 8
  %conv = sext i32 %i1 to i64
  %call1 = call noalias i8* @calloc(i64 %conv, i64 4) #9
  %i2 = bitcast i8* %call1 to float*
  %tobool2 = icmp ne float* %i2, null
  br i1 %tobool2, label %if.end, label %if.then3

if.then3:                                         ; preds = %if.then
  %width4 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i3 = load i32, i32* %width4, align 8
  %call5 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([48 x i8], [48 x i8]* @.str, i64 0, i64 0), i32 %i3)
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %if.then
  %width6 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i4 = load i32, i32* %width6, align 8
  %conv7 = sext i32 %i4 to i64
  %mul = mul i64 %conv7, 4
  %call8 = call i64 @quantum_memman(i64 %mul)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %width9 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i5 = load i32, i32* %width9, align 8
  %cmp = icmp slt i32 %i.0, %i5
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  br label %do.body

do.body:                                          ; preds = %do.cond, %for.body
  %call11 = call double (...) bitcast (double ()* @quantum_frand to double (...)*)()
  %mul12 = fmul double 2.000000e+00, %call11
  %sub = fsub double %mul12, 1.000000e+00
  %conv13 = fptrunc double %sub to float
  %call14 = call double (...) bitcast (double ()* @quantum_frand to double (...)*)()
  %mul15 = fmul double 2.000000e+00, %call14
  %sub16 = fsub double %mul15, 1.000000e+00
  %conv17 = fptrunc double %sub16 to float
  %mul18 = fmul float %conv13, %conv13
  %mul19 = fmul float %conv17, %conv17
  %add = fadd float %mul18, %mul19
  br label %do.cond

do.cond:                                          ; preds = %do.body
  %cmp20 = fcmp oge float %add, 1.000000e+00
  br i1 %cmp20, label %do.body, label %do.end

do.end:                                           ; preds = %do.cond
  %conv22 = fpext float %conv13 to double
  %conv23 = fpext float %add to double
  %call24 = call double @log(double %conv23) #9
  %mul25 = fmul double -2.000000e+00, %call24
  %conv26 = fpext float %add to double
  %div = fdiv double %mul25, %conv26
  %call27 = call double @sqrt(double %div) #9
  %mul28 = fmul double %conv22, %call27
  %conv29 = fptrunc double %mul28 to float
  %i6 = load float, float* @lambda, align 4
  %mul30 = fmul float 2.000000e+00, %i6
  %conv31 = fpext float %mul30 to double
  %call32 = call double @sqrt(double %conv31) #9
  %conv33 = fpext float %conv29 to double
  %mul34 = fmul double %conv33, %call32
  %conv35 = fptrunc double %mul34 to float
  %div36 = fdiv float %conv35, 2.000000e+00
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds float, float* %i2, i64 %idxprom
  store float %div36, float* %arrayidx, align 4
  br label %for.inc

for.inc:                                          ; preds = %do.end
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond37

for.cond37:                                       ; preds = %for.inc69, %for.end
  %i.1 = phi i32 [ 0, %for.end ], [ %inc70, %for.inc69 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i7 = load i32, i32* %size, align 4
  %cmp38 = icmp slt i32 %i.1, %i7
  br i1 %cmp38, label %for.body40, label %for.end71

for.body40:                                       ; preds = %for.cond37
  br label %for.cond41

for.cond41:                                       ; preds = %for.inc57, %for.body40
  %angle.0 = phi float [ 0.000000e+00, %for.body40 ], [ %angle.1, %for.inc57 ]
  %j.0 = phi i32 [ 0, %for.body40 ], [ %inc58, %for.inc57 ]
  %width42 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i8 = load i32, i32* %width42, align 8
  %cmp43 = icmp slt i32 %j.0, %i8
  br i1 %cmp43, label %for.body45, label %for.end59

for.body45:                                       ; preds = %for.cond41
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i9 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom46 = sext i32 %i.1 to i64
  %arrayidx47 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i9, i64 %idxprom46
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx47, i32 0, i32 1
  %i10 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %j.0 to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i10, %shl
  %tobool48 = icmp ne i64 %and, 0
  br i1 %tobool48, label %if.then49, label %if.else

if.then49:                                        ; preds = %for.body45
  %idxprom50 = sext i32 %j.0 to i64
  %arrayidx51 = getelementptr inbounds float, float* %i2, i64 %idxprom50
  %i11 = load float, float* %arrayidx51, align 4
  %add52 = fadd float %angle.0, %i11
  br label %if.end56

if.else:                                          ; preds = %for.body45
  %idxprom53 = sext i32 %j.0 to i64
  %arrayidx54 = getelementptr inbounds float, float* %i2, i64 %idxprom53
  %i12 = load float, float* %arrayidx54, align 4
  %sub55 = fsub float %angle.0, %i12
  br label %if.end56

if.end56:                                         ; preds = %if.else, %if.then49
  %angle.1 = phi float [ %add52, %if.then49 ], [ %sub55, %if.else ]
  br label %for.inc57

for.inc57:                                        ; preds = %if.end56
  %inc58 = add nsw i32 %j.0, 1
  br label %for.cond41

for.end59:                                        ; preds = %for.cond41
  %call60 = call <2 x float> @quantum_cexp(float %angle.0)
  %i13 = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call60, <2 x float>* %i13, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %node61 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i14 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node61, align 8
  %idxprom62 = sext i32 %i.1 to i64
  %arrayidx63 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i14, i64 %idxprom62
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx63, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %coerce.real
  %mul_bd = fmul float %amplitude.imag, %coerce.imag
  %mul_ad = fmul float %amplitude.real, %coerce.imag
  %mul_bc = fmul float %amplitude.imag, %coerce.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %for.end59
  %isnan_cmp64 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp64, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call65 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %coerce.real, float %coerce.imag) #9
  %i15 = bitcast { float, float }* %coerce66 to <2 x float>*
  store <2 x float> %call65, <2 x float>* %i15, align 4
  %coerce66.realp = getelementptr inbounds { float, float }, { float, float }* %coerce66, i32 0, i32 0
  %coerce66.real = load float, float* %coerce66.realp, align 4
  %coerce66.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce66, i32 0, i32 1
  %coerce66.imag = load float, float* %coerce66.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %for.end59
  %real_mul_phi = phi float [ %mul_r, %for.end59 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce66.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %for.end59 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce66.imag, %complex_mul_libcall ]
  %amplitude.realp67 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp68 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp67, align 8
  store float %imag_mul_phi, float* %amplitude.imagp68, align 4
  br label %for.inc69

for.inc69:                                        ; preds = %complex_mul_cont
  %inc70 = add nsw i32 %i.1, 1
  br label %for.cond37

for.end71:                                        ; preds = %for.cond37
  %i16 = bitcast float* %i2 to i8*
  call void @free(i8* %i16) #9
  %width72 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i17 = load i32, i32* %width72, align 8
  %sub73 = sub nsw i32 0, %i17
  %conv74 = sext i32 %sub73 to i64
  %mul75 = mul i64 %conv74, 4
  %call76 = call i64 @quantum_memman(i64 %mul75)
  br label %if.end77

if.end77:                                         ; preds = %for.end71, %entry
  ret void
}

; Function Attrs: nounwind
declare dso_local noalias i8* @calloc(i64, i64) #3

declare dso_local i32 @printf(i8*, ...) #4

; Function Attrs: noreturn nounwind
declare dso_local void @exit(i32) #5

; Function Attrs: nounwind
declare dso_local double @log(double) #3

; Function Attrs: nounwind
declare dso_local double @sqrt(double) #3

declare dso_local <2 x float> @__mulsc3(float, float, float, float)

; Function Attrs: nounwind
declare dso_local void @free(i8*) #3

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_exp_mod_n(i32 %N, i32 %x, i32 %width_input, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %mul = mul nsw i32 2, %width
  %add = add nsw i32 %mul, 2
  call void @quantum_sigma_x(i32 %add, %struct.quantum_reg_struct* %reg)
  br label %for.cond

for.cond:                                         ; preds = %for.inc9, %entry
  %i.0 = phi i32 [ 1, %entry ], [ %inc10, %for.inc9 ]
  %cmp = icmp sle i32 %i.0, %width_input
  br i1 %cmp, label %for.body, label %for.end11

for.body:                                         ; preds = %for.cond
  %rem = srem i32 %x, %N
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ 1, %for.body ], [ %inc, %for.inc ]
  %f.0 = phi i32 [ %rem, %for.body ], [ %rem5, %for.inc ]
  %cmp2 = icmp slt i32 %j.0, %i.0
  br i1 %cmp2, label %for.body3, label %for.end

for.body3:                                        ; preds = %for.cond1
  %mul4 = mul nsw i32 %f.0, %f.0
  %rem5 = srem i32 %mul4, %N
  br label %for.inc

for.inc:                                          ; preds = %for.body3
  %inc = add nsw i32 %j.0, 1
  br label %for.cond1

for.end:                                          ; preds = %for.cond1
  %mul6 = mul nsw i32 3, %width
  %add7 = add nsw i32 %mul6, 1
  %add8 = add nsw i32 %add7, %i.0
  call void @mul_mod_n(i32 %N, i32 %f.0, i32 %add8, i32 %width, %struct.quantum_reg_struct* %reg)
  br label %for.inc9

for.inc9:                                         ; preds = %for.end
  %inc10 = add nsw i32 %i.0, 1
  br label %for.cond

for.end11:                                        ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_cnot(i32 %control, i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %qec = alloca i32, align 4
  call void @quantum_qec_get_status(i32* %qec, i32* null)
  %i = load i32, i32* %qec, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  call void @quantum_cnot_ft(i32 %control, i32 %target, %struct.quantum_reg_struct* %reg)
  br label %if.end12

if.else:                                          ; preds = %entry
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 1, i32 %control, i32 %target)
  %tobool1 = icmp ne i32 %call, 0
  br i1 %tobool1, label %if.then2, label %if.end

if.then2:                                         ; preds = %if.else
  br label %if.end12

if.end:                                           ; preds = %if.else
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %control to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i3, %shl
  %tobool3 = icmp ne i64 %and, 0
  br i1 %tobool3, label %if.then4, label %if.end11

if.then4:                                         ; preds = %for.body
  %sh_prom5 = zext i32 %target to i64
  %shl6 = shl i64 1, %sh_prom5
  %node7 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node7, align 8
  %idxprom8 = sext i32 %i.0 to i64
  %arrayidx9 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom8
  %state10 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx9, i32 0, i32 1
  %i5 = load i64, i64* %state10, align 8
  %xor = xor i64 %i5, %shl6
  store i64 %xor, i64* %state10, align 8
  br label %if.end11

if.end11:                                         ; preds = %if.then4, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end11
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %if.end12

if.end12:                                         ; preds = %for.end, %if.then2, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_toffoli(i32 %control1, i32 %control2, i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %qec = alloca i32, align 4
  call void @quantum_qec_get_status(i32* %qec, i32* null)
  %i = load i32, i32* %qec, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  call void @quantum_toffoli_ft(i32 %control1, i32 %control2, i32 %target, %struct.quantum_reg_struct* %reg)
  br label %if.end22

if.else:                                          ; preds = %entry
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 2, i32 %control1, i32 %control2, i32 %target)
  %tobool1 = icmp ne i32 %call, 0
  br i1 %tobool1, label %if.then2, label %if.end

if.then2:                                         ; preds = %if.else
  br label %if.end22

if.end:                                           ; preds = %if.else
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %control1 to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i3, %shl
  %tobool3 = icmp ne i64 %and, 0
  br i1 %tobool3, label %if.then4, label %if.end21

if.then4:                                         ; preds = %for.body
  %node5 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node5, align 8
  %idxprom6 = sext i32 %i.0 to i64
  %arrayidx7 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom6
  %state8 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx7, i32 0, i32 1
  %i5 = load i64, i64* %state8, align 8
  %sh_prom9 = zext i32 %control2 to i64
  %shl10 = shl i64 1, %sh_prom9
  %and11 = and i64 %i5, %shl10
  %tobool12 = icmp ne i64 %and11, 0
  br i1 %tobool12, label %if.then13, label %if.end20

if.then13:                                        ; preds = %if.then4
  %sh_prom14 = zext i32 %target to i64
  %shl15 = shl i64 1, %sh_prom14
  %node16 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node16, align 8
  %idxprom17 = sext i32 %i.0 to i64
  %arrayidx18 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom17
  %state19 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx18, i32 0, i32 1
  %i7 = load i64, i64* %state19, align 8
  %xor = xor i64 %i7, %shl15
  store i64 %xor, i64* %state19, align 8
  br label %if.end20

if.end20:                                         ; preds = %if.then13, %if.then4
  br label %if.end21

if.end21:                                         ; preds = %if.end20, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end21
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %if.end22

if.end22:                                         ; preds = %for.end, %if.then2, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_unbounded_toffoli(i32 %controlling, %struct.quantum_reg_struct* %reg, ...) #0 {
entry:
  %bits = alloca [1 x %struct.__va_list_tag], align 16
  %conv = sext i32 %controlling to i64
  %mul = mul i64 %conv, 4
  %call = call noalias i8* @malloc(i64 %mul) #9
  %i = bitcast i8* %call to i32*
  %tobool = icmp ne i32* %i, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %call1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.1, i64 0, i64 0), i32 %controlling)
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %entry
  %conv2 = sext i32 %controlling to i64
  %mul3 = mul i64 %conv2, 4
  %call4 = call i64 @quantum_memman(i64 %mul3)
  %arraydecay = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %bits, i64 0, i64 0
  %arraydecay5 = bitcast %struct.__va_list_tag* %arraydecay to i8*
  call void @llvm.va_start(i8* %arraydecay5)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %i.0, %controlling
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %arraydecay7 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %bits, i64 0, i64 0
  %gp_offset_p = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay7, i32 0, i32 0
  %gp_offset = load i32, i32* %gp_offset_p, align 16
  %fits_in_gp = icmp ule i32 %gp_offset, 40
  br i1 %fits_in_gp, label %vaarg.in_reg, label %vaarg.in_mem

vaarg.in_reg:                                     ; preds = %for.body
  %i1 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay7, i32 0, i32 3
  %reg_save_area = load i8*, i8** %i1, align 16
  %i2 = getelementptr i8, i8* %reg_save_area, i32 %gp_offset
  %i3 = bitcast i8* %i2 to i32*
  %i4 = add i32 %gp_offset, 8
  store i32 %i4, i32* %gp_offset_p, align 16
  br label %vaarg.end

vaarg.in_mem:                                     ; preds = %for.body
  %overflow_arg_area_p = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay7, i32 0, i32 2
  %overflow_arg_area = load i8*, i8** %overflow_arg_area_p, align 8
  %i5 = bitcast i8* %overflow_arg_area to i32*
  %overflow_arg_area.next = getelementptr i8, i8* %overflow_arg_area, i32 8
  store i8* %overflow_arg_area.next, i8** %overflow_arg_area_p, align 8
  br label %vaarg.end

vaarg.end:                                        ; preds = %vaarg.in_mem, %vaarg.in_reg
  %vaarg.addr = phi i32* [ %i3, %vaarg.in_reg ], [ %i5, %vaarg.in_mem ]
  %i6 = load i32, i32* %vaarg.addr, align 4
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i, i64 %idxprom
  store i32 %i6, i32* %arrayidx, align 4
  br label %for.inc

for.inc:                                          ; preds = %vaarg.end
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %arraydecay8 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %bits, i64 0, i64 0
  %gp_offset_p9 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay8, i32 0, i32 0
  %gp_offset10 = load i32, i32* %gp_offset_p9, align 16
  %fits_in_gp11 = icmp ule i32 %gp_offset10, 40
  br i1 %fits_in_gp11, label %vaarg.in_reg12, label %vaarg.in_mem14

vaarg.in_reg12:                                   ; preds = %for.end
  %i7 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay8, i32 0, i32 3
  %reg_save_area13 = load i8*, i8** %i7, align 16
  %i8 = getelementptr i8, i8* %reg_save_area13, i32 %gp_offset10
  %i9 = bitcast i8* %i8 to i32*
  %i10 = add i32 %gp_offset10, 8
  store i32 %i10, i32* %gp_offset_p9, align 16
  br label %vaarg.end18

vaarg.in_mem14:                                   ; preds = %for.end
  %overflow_arg_area_p15 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay8, i32 0, i32 2
  %overflow_arg_area16 = load i8*, i8** %overflow_arg_area_p15, align 8
  %i11 = bitcast i8* %overflow_arg_area16 to i32*
  %overflow_arg_area.next17 = getelementptr i8, i8* %overflow_arg_area16, i32 8
  store i8* %overflow_arg_area.next17, i8** %overflow_arg_area_p15, align 8
  br label %vaarg.end18

vaarg.end18:                                      ; preds = %vaarg.in_mem14, %vaarg.in_reg12
  %vaarg.addr19 = phi i32* [ %i9, %vaarg.in_reg12 ], [ %i11, %vaarg.in_mem14 ]
  %i12 = load i32, i32* %vaarg.addr19, align 4
  %arraydecay20 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %bits, i64 0, i64 0
  %arraydecay2021 = bitcast %struct.__va_list_tag* %arraydecay20 to i8*
  call void @llvm.va_end(i8* %arraydecay2021)
  br label %for.cond22

for.cond22:                                       ; preds = %for.inc48, %vaarg.end18
  %i.1 = phi i32 [ 0, %vaarg.end18 ], [ %inc49, %for.inc48 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i13 = load i32, i32* %size, align 4
  %cmp23 = icmp slt i32 %i.1, %i13
  br i1 %cmp23, label %for.body25, label %for.end50

for.body25:                                       ; preds = %for.cond22
  br label %for.cond26

for.cond26:                                       ; preds = %for.inc35, %for.body25
  %j.0 = phi i32 [ 0, %for.body25 ], [ %inc36, %for.inc35 ]
  %cmp27 = icmp slt i32 %j.0, %controlling
  br i1 %cmp27, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %for.cond26
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i14 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom29 = sext i32 %i.1 to i64
  %arrayidx30 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i14, i64 %idxprom29
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx30, i32 0, i32 1
  %i15 = load i64, i64* %state, align 8
  %idxprom31 = sext i32 %j.0 to i64
  %arrayidx32 = getelementptr inbounds i32, i32* %i, i64 %idxprom31
  %i16 = load i32, i32* %arrayidx32, align 4
  %sh_prom = zext i32 %i16 to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i15, %shl
  %tobool33 = icmp ne i64 %and, 0
  br label %land.end

land.end:                                         ; preds = %land.rhs, %for.cond26
  %i17 = phi i1 [ false, %for.cond26 ], [ %tobool33, %land.rhs ]
  br i1 %i17, label %for.body34, label %for.end37

for.body34:                                       ; preds = %land.end
  br label %for.inc35

for.inc35:                                        ; preds = %for.body34
  %inc36 = add nsw i32 %j.0, 1
  br label %for.cond26

for.end37:                                        ; preds = %land.end
  %cmp38 = icmp eq i32 %j.0, %controlling
  br i1 %cmp38, label %if.then40, label %if.end47

if.then40:                                        ; preds = %for.end37
  %sh_prom41 = zext i32 %i12 to i64
  %shl42 = shl i64 1, %sh_prom41
  %node43 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i18 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node43, align 8
  %idxprom44 = sext i32 %i.1 to i64
  %arrayidx45 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i18, i64 %idxprom44
  %state46 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx45, i32 0, i32 1
  %i19 = load i64, i64* %state46, align 8
  %xor = xor i64 %i19, %shl42
  store i64 %xor, i64* %state46, align 8
  br label %if.end47

if.end47:                                         ; preds = %if.then40, %for.end37
  br label %for.inc48

for.inc48:                                        ; preds = %if.end47
  %inc49 = add nsw i32 %i.1, 1
  br label %for.cond22

for.end50:                                        ; preds = %for.cond22
  %i20 = bitcast i32* %i to i8*
  call void @free(i8* %i20) #9
  %sub = sub nsw i32 0, %controlling
  %conv51 = sext i32 %sub to i64
  %mul52 = mul i64 %conv51, 4
  %call53 = call i64 @quantum_memman(i64 %mul52)
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i64) #3

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_start(i8*) #6

; Function Attrs: nofree nosync nounwind willreturn
declare void @llvm.va_end(i8*) #6

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_sigma_x(i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %qec = alloca i32, align 4
  call void @quantum_qec_get_status(i32* %qec, i32* null)
  %i = load i32, i32* %qec, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  call void @quantum_sigma_x_ft(i32 %target, %struct.quantum_reg_struct* %reg)
  br label %if.end3

if.else:                                          ; preds = %entry
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 3, i32 %target)
  %tobool1 = icmp ne i32 %call, 0
  br i1 %tobool1, label %if.then2, label %if.end

if.then2:                                         ; preds = %if.else
  br label %if.end3

if.end:                                           ; preds = %if.else
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %sh_prom = zext i32 %target to i64
  %shl = shl i64 1, %sh_prom
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %xor = xor i64 %i3, %shl
  store i64 %xor, i64* %state, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %if.end3

if.end3:                                          ; preds = %for.end, %if.then2, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_sigma_y(i32 %target, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %coerce31 = alloca { float, float }, align 4
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 4, i32 %target)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %sh_prom = zext i32 %target to i64
  %shl = shl i64 1, %sh_prom
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i2 = load i64, i64* %state, align 8
  %xor = xor i64 %i2, %shl
  store i64 %xor, i64* %state, align 8
  %node1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node1, align 8
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom2
  %state4 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx3, i32 0, i32 1
  %i4 = load i64, i64* %state4, align 8
  %sh_prom5 = zext i32 %target to i64
  %shl6 = shl i64 1, %sh_prom5
  %and = and i64 %i4, %shl6
  %tobool7 = icmp ne i64 %and, 0
  br i1 %tobool7, label %if.then8, label %if.else

if.then8:                                         ; preds = %for.body
  %node9 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i5 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node9, align 8
  %idxprom10 = sext i32 %i.0 to i64
  %arrayidx11 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i5, i64 %idxprom10
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx11, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, 0.000000e+00
  %mul_bd = fmul float %amplitude.imag, 1.000000e+00
  %mul_ad = fmul float %amplitude.real, 1.000000e+00
  %mul_bc = fmul float %amplitude.imag, 0.000000e+00
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then8
  %isnan_cmp12 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp12, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call13 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float 0.000000e+00, float 1.000000e+00) #9
  %i6 = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call13, <2 x float>* %i6, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then8
  %real_mul_phi = phi float [ %mul_r, %if.then8 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then8 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce.imag, %complex_mul_libcall ]
  %amplitude.realp14 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp15 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp14, align 8
  store float %imag_mul_phi, float* %amplitude.imagp15, align 4
  br label %if.end37

if.else:                                          ; preds = %for.body
  %node16 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i7 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node16, align 8
  %idxprom17 = sext i32 %i.0 to i64
  %arrayidx18 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i7, i64 %idxprom17
  %amplitude19 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx18, i32 0, i32 0
  %amplitude19.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude19, i32 0, i32 0
  %amplitude19.real = load float, float* %amplitude19.realp, align 8
  %amplitude19.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude19, i32 0, i32 1
  %amplitude19.imag = load float, float* %amplitude19.imagp, align 4
  %mul_ac20 = fmul float %amplitude19.real, -0.000000e+00
  %mul_bd21 = fmul float %amplitude19.imag, -1.000000e+00
  %mul_ad22 = fmul float %amplitude19.real, -1.000000e+00
  %mul_bc23 = fmul float %amplitude19.imag, -0.000000e+00
  %mul_r24 = fsub float %mul_ac20, %mul_bd21
  %mul_i25 = fadd float %mul_ad22, %mul_bc23
  %isnan_cmp26 = fcmp uno float %mul_r24, %mul_r24
  br i1 %isnan_cmp26, label %complex_mul_imag_nan27, label %complex_mul_cont32, !prof !2

complex_mul_imag_nan27:                           ; preds = %if.else
  %isnan_cmp28 = fcmp uno float %mul_i25, %mul_i25
  br i1 %isnan_cmp28, label %complex_mul_libcall29, label %complex_mul_cont32, !prof !2

complex_mul_libcall29:                            ; preds = %complex_mul_imag_nan27
  %call30 = call <2 x float> @__mulsc3(float %amplitude19.real, float %amplitude19.imag, float -0.000000e+00, float -1.000000e+00) #9
  %i8 = bitcast { float, float }* %coerce31 to <2 x float>*
  store <2 x float> %call30, <2 x float>* %i8, align 4
  %coerce31.realp = getelementptr inbounds { float, float }, { float, float }* %coerce31, i32 0, i32 0
  %coerce31.real = load float, float* %coerce31.realp, align 4
  %coerce31.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce31, i32 0, i32 1
  %coerce31.imag = load float, float* %coerce31.imagp, align 4
  br label %complex_mul_cont32

complex_mul_cont32:                               ; preds = %complex_mul_libcall29, %complex_mul_imag_nan27, %if.else
  %real_mul_phi33 = phi float [ %mul_r24, %if.else ], [ %mul_r24, %complex_mul_imag_nan27 ], [ %coerce31.real, %complex_mul_libcall29 ]
  %imag_mul_phi34 = phi float [ %mul_i25, %if.else ], [ %mul_i25, %complex_mul_imag_nan27 ], [ %coerce31.imag, %complex_mul_libcall29 ]
  %amplitude19.realp35 = getelementptr inbounds { float, float }, { float, float }* %amplitude19, i32 0, i32 0
  %amplitude19.imagp36 = getelementptr inbounds { float, float }, { float, float }* %amplitude19, i32 0, i32 1
  store float %real_mul_phi33, float* %amplitude19.realp35, align 8
  store float %imag_mul_phi34, float* %amplitude19.imagp36, align 4
  br label %if.end37

if.end37:                                         ; preds = %complex_mul_cont32, %complex_mul_cont
  br label %for.inc

for.inc:                                          ; preds = %if.end37
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_sigma_z(i32 %target, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 5, i32 %target)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i2 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %target to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i2, %shl
  %tobool1 = icmp ne i64 %and, 0
  br i1 %tobool1, label %if.then2, label %if.end10

if.then2:                                         ; preds = %for.body
  %node3 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node3, align 8
  %idxprom4 = sext i32 %i.0 to i64
  %arrayidx5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom4
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx5, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, -1.000000e+00
  %mul_bd = fmul float %amplitude.imag, 0.000000e+00
  %mul_ad = fmul float %amplitude.real, 0.000000e+00
  %mul_bc = fmul float %amplitude.imag, -1.000000e+00
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then2
  %isnan_cmp6 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp6, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call7 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float -1.000000e+00, float 0.000000e+00) #9
  %i4 = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call7, <2 x float>* %i4, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then2
  %real_mul_phi = phi float [ %mul_r, %if.then2 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then2 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce.imag, %complex_mul_libcall ]
  %amplitude.realp8 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp9 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp8, align 8
  store float %imag_mul_phi, float* %amplitude.imagp9, align 4
  br label %if.end10

if.end10:                                         ; preds = %complex_mul_cont, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end10
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_swaptheleads(i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %qec = alloca i32, align 4
  call void @quantum_qec_get_status(i32* %qec, i32* null)
  %i = load i32, i32* %qec, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.then
  %i.0 = phi i32 [ 0, %if.then ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %i.0, %width
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %add = add nsw i32 %width, %i.0
  call void @quantum_cnot(i32 %i.0, i32 %add, %struct.quantum_reg_struct* %reg)
  %add1 = add nsw i32 %width, %i.0
  call void @quantum_cnot(i32 %add1, i32 %i.0, %struct.quantum_reg_struct* %reg)
  %add2 = add nsw i32 %width, %i.0
  call void @quantum_cnot(i32 %i.0, i32 %add2, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %if.end43

if.else:                                          ; preds = %entry
  br label %for.cond3

for.cond3:                                        ; preds = %for.inc40, %if.else
  %i.1 = phi i32 [ 0, %if.else ], [ %inc41, %for.inc40 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp4 = icmp slt i32 %i.1, %i1
  br i1 %cmp4, label %for.body5, label %for.end42

for.body5:                                        ; preds = %for.cond3
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 14, i32 %width)
  %tobool6 = icmp ne i32 %call, 0
  br i1 %tobool6, label %if.then7, label %if.end

if.then7:                                         ; preds = %for.body5
  br label %if.end43

if.end:                                           ; preds = %for.body5
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.1 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %width to i64
  %shl = shl i64 1, %sh_prom
  %rem = urem i64 %i3, %shl
  %conv = trunc i64 %rem to i32
  br label %for.cond8

for.cond8:                                        ; preds = %for.inc22, %if.end
  %j.0 = phi i32 [ 0, %if.end ], [ %inc23, %for.inc22 ]
  %pat2.0 = phi i32 [ 0, %if.end ], [ %conv21, %for.inc22 ]
  %cmp9 = icmp slt i32 %j.0, %width
  br i1 %cmp9, label %for.body11, label %for.end24

for.body11:                                       ; preds = %for.cond8
  %node12 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node12, align 8
  %idxprom13 = sext i32 %i.1 to i64
  %arrayidx14 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom13
  %state15 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx14, i32 0, i32 1
  %i5 = load i64, i64* %state15, align 8
  %add16 = add nsw i32 %width, %j.0
  %sh_prom17 = zext i32 %add16 to i64
  %shl18 = shl i64 1, %sh_prom17
  %and = and i64 %i5, %shl18
  %conv19 = sext i32 %pat2.0 to i64
  %add20 = add i64 %conv19, %and
  %conv21 = trunc i64 %add20 to i32
  br label %for.inc22

for.inc22:                                        ; preds = %for.body11
  %inc23 = add nsw i32 %j.0, 1
  br label %for.cond8

for.end24:                                        ; preds = %for.cond8
  %node25 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node25, align 8
  %idxprom26 = sext i32 %i.1 to i64
  %arrayidx27 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom26
  %state28 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx27, i32 0, i32 1
  %i7 = load i64, i64* %state28, align 8
  %add29 = add nsw i32 %conv, %pat2.0
  %conv30 = sext i32 %add29 to i64
  %sub = sub i64 %i7, %conv30
  %shl31 = shl i32 %conv, %width
  %conv32 = sext i32 %shl31 to i64
  %add33 = add i64 %sub, %conv32
  %shr = ashr i32 %pat2.0, %width
  %conv34 = sext i32 %shr to i64
  %add35 = add i64 %add33, %conv34
  %node36 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node36, align 8
  %idxprom37 = sext i32 %i.1 to i64
  %arrayidx38 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i8, i64 %idxprom37
  %state39 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx38, i32 0, i32 1
  store i64 %add35, i64* %state39, align 8
  br label %for.inc40

for.inc40:                                        ; preds = %for.end24
  %inc41 = add nsw i32 %i.1, 1
  br label %for.cond3

for.end42:                                        ; preds = %for.cond3
  br label %if.end43

if.end43:                                         ; preds = %for.end42, %if.then7, %for.end
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_swaptheleads_omuln_controlled(i32 %control, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %i.0, %width
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %add = add nsw i32 %width, %i.0
  %mul = mul nsw i32 2, %width
  %add1 = add nsw i32 %mul, %i.0
  %add2 = add nsw i32 %add1, 2
  call void @quantum_toffoli(i32 %control, i32 %add, i32 %add2, %struct.quantum_reg_struct* %reg)
  %mul3 = mul nsw i32 2, %width
  %add4 = add nsw i32 %mul3, %i.0
  %add5 = add nsw i32 %add4, 2
  %add6 = add nsw i32 %width, %i.0
  call void @quantum_toffoli(i32 %control, i32 %add5, i32 %add6, %struct.quantum_reg_struct* %reg)
  %add7 = add nsw i32 %width, %i.0
  %mul8 = mul nsw i32 2, %width
  %add9 = add nsw i32 %mul8, %i.0
  %add10 = add nsw i32 %add9, 2
  call void @quantum_toffoli(i32 %control, i32 %add7, i32 %add10, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_gate1(i32 %target, i64 %m.coerce0, { float, float }* %m.coerce1, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %m = alloca %struct.quantum_matrix_struct, align 8
  %t = alloca { float, float }, align 4
  %tnot = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce39 = alloca { float, float }, align 4
  %coerce166 = alloca { float, float }, align 4
  %coerce182 = alloca { float, float }, align 4
  %coerce207 = alloca { float, float }, align 4
  %coerce228 = alloca { float, float }, align 4
  %coerce261 = alloca { float, float }, align 4
  %coerce282 = alloca { float, float }, align 4
  %coerce310 = alloca { float, float }, align 4
  %coerce331 = alloca { float, float }, align 4
  %coerce345 = alloca { float, float }, align 4
  %coerce356 = alloca { float, float }, align 4
  %coerce395 = alloca { float, float }, align 4
  %coerce421 = alloca { float, float }, align 4
  %coerce457 = alloca { float, float }, align 4
  %i = bitcast %struct.quantum_matrix_struct* %m to { i64, { float, float }* }*
  %i1 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 0
  store i64 %m.coerce0, i64* %i1, align 8
  %i2 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 1
  store { float, float }* %m.coerce1, { float, float }** %i2, align 8
  %tnot.realp = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.imagp = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  store float 0.000000e+00, float* %tnot.realp, align 4
  store float 0.000000e+00, float* %tnot.imagp, align 4
  %cols = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i3 = load i32, i32* %cols, align 4
  %cmp = icmp ne i32 %i3, 2
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %rows = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i4 = load i32, i32* %rows, align 8
  %cmp1 = icmp ne i32 %i4, 2
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.1.4, i64 0, i64 0))
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %lor.lhs.false
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i5 = load i32, i32* %hashw, align 8
  %shl = shl i32 1, %i5
  %cmp2 = icmp slt i32 %i.0, %shl
  br i1 %cmp2, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i6 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i6, i64 %idxprom
  store i32 0, i32* %arrayidx, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond3

for.cond3:                                        ; preds = %for.inc8, %for.end
  %i.1 = phi i32 [ 0, %for.end ], [ %inc9, %for.inc8 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i7 = load i32, i32* %size, align 4
  %cmp4 = icmp slt i32 %i.1, %i7
  br i1 %cmp4, label %for.body5, label %for.end10

for.body5:                                        ; preds = %for.cond3
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom6 = sext i32 %i.1 to i64
  %arrayidx7 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i8, i64 %idxprom6
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx7, i32 0, i32 1
  %i9 = load i64, i64* %state, align 8
  call void @quantum_add_hash(i64 %i9, i32 %i.1, %struct.quantum_reg_struct* %reg)
  br label %for.inc8

for.inc8:                                         ; preds = %for.body5
  %inc9 = add nsw i32 %i.1, 1
  br label %for.cond3

for.end10:                                        ; preds = %for.cond3
  br label %for.cond11

for.cond11:                                       ; preds = %for.inc57, %for.end10
  %i.2 = phi i32 [ 0, %for.end10 ], [ %inc58, %for.inc57 ]
  %addsize.0 = phi i32 [ 0, %for.end10 ], [ %addsize.3, %for.inc57 ]
  %size12 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i10 = load i32, i32* %size12, align 4
  %cmp13 = icmp slt i32 %i.2, %i10
  br i1 %cmp13, label %for.body14, label %for.end59

for.body14:                                       ; preds = %for.cond11
  %node15 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i11 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node15, align 8
  %idxprom16 = sext i32 %i.2 to i64
  %arrayidx17 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i11, i64 %idxprom16
  %state18 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx17, i32 0, i32 1
  %i12 = load i64, i64* %state18, align 8
  %sh_prom = zext i32 %target to i64
  %shl19 = shl i64 1, %sh_prom
  %xor = xor i64 %i12, %shl19
  %call20 = call i32 @quantum_get_state(i64 %xor, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg)
  %cmp21 = icmp eq i32 %call20, -1
  br i1 %cmp21, label %if.then22, label %if.end56

if.then22:                                        ; preds = %for.body14
  %t23 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i13 = load { float, float }*, { float, float }** %t23, align 8
  %arrayidx24 = getelementptr inbounds { float, float }, { float, float }* %i13, i64 1
  %arrayidx24.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx24, i32 0, i32 0
  %arrayidx24.real = load float, float* %arrayidx24.realp, align 4
  %arrayidx24.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx24, i32 0, i32 1
  %arrayidx24.imag = load float, float* %arrayidx24.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %arrayidx24.real, float* %coerce.realp, align 4
  store float %arrayidx24.imag, float* %coerce.imagp, align 4
  %i14 = bitcast { float, float }* %coerce to <2 x float>*
  %i15 = load <2 x float>, <2 x float>* %i14, align 4
  %call25 = call float @quantum_prob_inline.5(<2 x float> %i15)
  %conv = fpext float %call25 to double
  %cmp26 = fcmp ogt double %conv, 1.000000e-09
  br i1 %cmp26, label %land.lhs.true, label %if.end36

land.lhs.true:                                    ; preds = %if.then22
  %node28 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i16 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node28, align 8
  %idxprom29 = sext i32 %i.2 to i64
  %arrayidx30 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i16, i64 %idxprom29
  %state31 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx30, i32 0, i32 1
  %i17 = load i64, i64* %state31, align 8
  %sh_prom32 = zext i32 %target to i64
  %shl33 = shl i64 1, %sh_prom32
  %and = and i64 %i17, %shl33
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %if.then34, label %if.end36

if.then34:                                        ; preds = %land.lhs.true
  %inc35 = add nsw i32 %addsize.0, 1
  br label %if.end36

if.end36:                                         ; preds = %if.then34, %land.lhs.true, %if.then22
  %addsize.1 = phi i32 [ %inc35, %if.then34 ], [ %addsize.0, %land.lhs.true ], [ %addsize.0, %if.then22 ]
  %t37 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i18 = load { float, float }*, { float, float }** %t37, align 8
  %arrayidx38 = getelementptr inbounds { float, float }, { float, float }* %i18, i64 2
  %arrayidx38.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx38, i32 0, i32 0
  %arrayidx38.real = load float, float* %arrayidx38.realp, align 4
  %arrayidx38.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx38, i32 0, i32 1
  %arrayidx38.imag = load float, float* %arrayidx38.imagp, align 4
  %coerce39.realp = getelementptr inbounds { float, float }, { float, float }* %coerce39, i32 0, i32 0
  %coerce39.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce39, i32 0, i32 1
  store float %arrayidx38.real, float* %coerce39.realp, align 4
  store float %arrayidx38.imag, float* %coerce39.imagp, align 4
  %i19 = bitcast { float, float }* %coerce39 to <2 x float>*
  %i20 = load <2 x float>, <2 x float>* %i19, align 4
  %call40 = call float @quantum_prob_inline.5(<2 x float> %i20)
  %conv41 = fpext float %call40 to double
  %cmp42 = fcmp ogt double %conv41, 1.000000e-09
  br i1 %cmp42, label %land.lhs.true44, label %if.end55

land.lhs.true44:                                  ; preds = %if.end36
  %node45 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i21 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node45, align 8
  %idxprom46 = sext i32 %i.2 to i64
  %arrayidx47 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i21, i64 %idxprom46
  %state48 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx47, i32 0, i32 1
  %i22 = load i64, i64* %state48, align 8
  %sh_prom49 = zext i32 %target to i64
  %shl50 = shl i64 1, %sh_prom49
  %and51 = and i64 %i22, %shl50
  %tobool52 = icmp ne i64 %and51, 0
  br i1 %tobool52, label %if.end55, label %if.then53

if.then53:                                        ; preds = %land.lhs.true44
  %inc54 = add nsw i32 %addsize.1, 1
  br label %if.end55

if.end55:                                         ; preds = %if.then53, %land.lhs.true44, %if.end36
  %addsize.2 = phi i32 [ %addsize.1, %land.lhs.true44 ], [ %inc54, %if.then53 ], [ %addsize.1, %if.end36 ]
  br label %if.end56

if.end56:                                         ; preds = %if.end55, %for.body14
  %addsize.3 = phi i32 [ %addsize.2, %if.end55 ], [ %addsize.0, %for.body14 ]
  br label %for.inc57

for.inc57:                                        ; preds = %if.end56
  %inc58 = add nsw i32 %i.2, 1
  br label %for.cond11

for.end59:                                        ; preds = %for.cond11
  %node60 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i23 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node60, align 8
  %i24 = bitcast %struct.quantum_reg_node_struct* %i23 to i8*
  %size61 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i25 = load i32, i32* %size61, align 4
  %add = add nsw i32 %i25, %addsize.0
  %conv62 = sext i32 %add to i64
  %mul = mul i64 %conv62, 16
  %call63 = call i8* @realloc(i8* %i24, i64 %mul) #9
  %i26 = bitcast i8* %call63 to %struct.quantum_reg_node_struct*
  %node64 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i26, %struct.quantum_reg_node_struct** %node64, align 8
  %node65 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i27 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node65, align 8
  %tobool66 = icmp ne %struct.quantum_reg_node_struct* %i27, null
  br i1 %tobool66, label %if.end71, label %if.then67

if.then67:                                        ; preds = %for.end59
  %size68 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i28 = load i32, i32* %size68, align 4
  %add69 = add nsw i32 %i28, %addsize.0
  %call70 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.2, i64 0, i64 0), i32 %add69)
  call void @exit(i32 1) #10
  unreachable

if.end71:                                         ; preds = %for.end59
  %conv72 = sext i32 %addsize.0 to i64
  %mul73 = mul i64 %conv72, 16
  %call74 = call i64 @quantum_memman(i64 %mul73)
  br label %for.cond75

for.cond75:                                       ; preds = %for.inc90, %if.end71
  %i.3 = phi i32 [ 0, %if.end71 ], [ %inc91, %for.inc90 ]
  %cmp76 = icmp slt i32 %i.3, %addsize.0
  br i1 %cmp76, label %for.body78, label %for.end92

for.body78:                                       ; preds = %for.cond75
  %node79 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i29 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node79, align 8
  %size80 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i30 = load i32, i32* %size80, align 4
  %add81 = add nsw i32 %i.3, %i30
  %idxprom82 = sext i32 %add81 to i64
  %arrayidx83 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i29, i64 %idxprom82
  %state84 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx83, i32 0, i32 1
  store i64 0, i64* %state84, align 8
  %node85 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i31 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node85, align 8
  %size86 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i32 = load i32, i32* %size86, align 4
  %add87 = add nsw i32 %i.3, %i32
  %idxprom88 = sext i32 %add87 to i64
  %arrayidx89 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i31, i64 %idxprom88
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx89, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float 0.000000e+00, float* %amplitude.realp, align 8
  store float 0.000000e+00, float* %amplitude.imagp, align 4
  br label %for.inc90

for.inc90:                                        ; preds = %for.body78
  %inc91 = add nsw i32 %i.3, 1
  br label %for.cond75

for.end92:                                        ; preds = %for.cond75
  %size93 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i33 = load i32, i32* %size93, align 4
  %add94 = add nsw i32 %i33, %addsize.0
  %conv95 = sext i32 %add94 to i64
  %call96 = call noalias i8* @calloc(i64 %conv95, i64 1) #9
  %tobool97 = icmp ne i8* %call96, null
  br i1 %tobool97, label %if.end104, label %if.then98

if.then98:                                        ; preds = %for.end92
  %size99 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i34 = load i32, i32* %size99, align 4
  %add100 = add nsw i32 %i34, %addsize.0
  %conv101 = sext i32 %add100 to i64
  %mul102 = mul i64 %conv101, 1
  %call103 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.3, i64 0, i64 0), i64 %mul102)
  call void @exit(i32 1) #10
  unreachable

if.end104:                                        ; preds = %for.end92
  %size105 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i35 = load i32, i32* %size105, align 4
  %conv106 = sext i32 %i35 to i64
  %conv107 = sext i32 %addsize.0 to i64
  %mul108 = mul i64 %conv107, 1
  %add109 = add i64 %conv106, %mul108
  %call110 = call i64 @quantum_memman(i64 %add109)
  %size111 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i36 = load i32, i32* %size111, align 4
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i37 = load i32, i32* %width, align 8
  %sh_prom112 = zext i32 %i37 to i64
  %shl113 = shl i64 1, %sh_prom112
  %conv114 = uitofp i64 %shl113 to double
  %div = fdiv double 1.000000e+00, %conv114
  %div115 = fdiv double %div, 1.000000e+06
  %conv116 = fptrunc double %div115 to float
  br label %for.cond117

for.cond117:                                      ; preds = %for.inc439, %if.end104
  %k.0 = phi i32 [ %i36, %if.end104 ], [ %k.2, %for.inc439 ]
  %i.4 = phi i32 [ 0, %if.end104 ], [ %inc440, %for.inc439 ]
  %size118 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i38 = load i32, i32* %size118, align 4
  %cmp119 = icmp slt i32 %i.4, %i38
  br i1 %cmp119, label %for.body121, label %for.end441

for.body121:                                      ; preds = %for.cond117
  %idxprom122 = sext i32 %i.4 to i64
  %arrayidx123 = getelementptr inbounds i8, i8* %call96, i64 %idxprom122
  %i39 = load i8, i8* %arrayidx123, align 1
  %tobool124 = icmp ne i8 %i39, 0
  br i1 %tobool124, label %if.end438, label %if.then125

if.then125:                                       ; preds = %for.body121
  %node126 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i40 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node126, align 8
  %idxprom127 = sext i32 %i.4 to i64
  %arrayidx128 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i40, i64 %idxprom127
  %state129 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx128, i32 0, i32 1
  %i41 = load i64, i64* %state129, align 8
  %sh_prom130 = zext i32 %target to i64
  %shl131 = shl i64 1, %sh_prom130
  %and132 = and i64 %i41, %shl131
  %conv133 = trunc i64 %and132 to i32
  %tnot.realp134 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.imagp135 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  store float 0.000000e+00, float* %tnot.realp134, align 4
  store float 0.000000e+00, float* %tnot.imagp135, align 4
  %node136 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i42 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node136, align 8
  %idxprom137 = sext i32 %i.4 to i64
  %arrayidx138 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i42, i64 %idxprom137
  %state139 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx138, i32 0, i32 1
  %i43 = load i64, i64* %state139, align 8
  %sh_prom140 = zext i32 %target to i64
  %shl141 = shl i64 1, %sh_prom140
  %xor142 = xor i64 %i43, %shl141
  %call143 = call i32 @quantum_get_state(i64 %xor142, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg)
  %node144 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i44 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node144, align 8
  %idxprom145 = sext i32 %i.4 to i64
  %arrayidx146 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i44, i64 %idxprom145
  %amplitude147 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx146, i32 0, i32 0
  %amplitude147.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude147, i32 0, i32 0
  %amplitude147.real = load float, float* %amplitude147.realp, align 8
  %amplitude147.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude147, i32 0, i32 1
  %amplitude147.imag = load float, float* %amplitude147.imagp, align 4
  %t.realp = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.imagp = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  store float %amplitude147.real, float* %t.realp, align 4
  store float %amplitude147.imag, float* %t.imagp, align 4
  %cmp148 = icmp sge i32 %call143, 0
  br i1 %cmp148, label %if.then150, label %if.end157

if.then150:                                       ; preds = %if.then125
  %node151 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i45 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node151, align 8
  %idxprom152 = sext i32 %call143 to i64
  %arrayidx153 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i45, i64 %idxprom152
  %amplitude154 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx153, i32 0, i32 0
  %amplitude154.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude154, i32 0, i32 0
  %amplitude154.real = load float, float* %amplitude154.realp, align 8
  %amplitude154.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude154, i32 0, i32 1
  %amplitude154.imag = load float, float* %amplitude154.imagp, align 4
  %tnot.realp155 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.imagp156 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  store float %amplitude154.real, float* %tnot.realp155, align 4
  store float %amplitude154.imag, float* %tnot.imagp156, align 4
  br label %if.end157

if.end157:                                        ; preds = %if.then150, %if.then125
  %tobool158 = icmp ne i32 %conv133, 0
  br i1 %tobool158, label %if.then159, label %if.else

if.then159:                                       ; preds = %if.end157
  %t160 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i46 = load { float, float }*, { float, float }** %t160, align 8
  %arrayidx161 = getelementptr inbounds { float, float }, { float, float }* %i46, i64 2
  %arrayidx161.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx161, i32 0, i32 0
  %arrayidx161.real = load float, float* %arrayidx161.realp, align 4
  %arrayidx161.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx161, i32 0, i32 1
  %arrayidx161.imag = load float, float* %arrayidx161.imagp, align 4
  %tnot.realp162 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real = load float, float* %tnot.realp162, align 4
  %tnot.imagp163 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag = load float, float* %tnot.imagp163, align 4
  %mul_ac = fmul float %arrayidx161.real, %tnot.real
  %mul_bd = fmul float %arrayidx161.imag, %tnot.imag
  %mul_ad = fmul float %arrayidx161.real, %tnot.imag
  %mul_bc = fmul float %arrayidx161.imag, %tnot.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then159
  %isnan_cmp164 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp164, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call165 = call <2 x float> @__mulsc3(float %arrayidx161.real, float %arrayidx161.imag, float %tnot.real, float %tnot.imag) #9
  %i47 = bitcast { float, float }* %coerce166 to <2 x float>*
  store <2 x float> %call165, <2 x float>* %i47, align 4
  %coerce166.realp = getelementptr inbounds { float, float }, { float, float }* %coerce166, i32 0, i32 0
  %coerce166.real = load float, float* %coerce166.realp, align 4
  %coerce166.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce166, i32 0, i32 1
  %coerce166.imag = load float, float* %coerce166.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then159
  %real_mul_phi = phi float [ %mul_r, %if.then159 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce166.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then159 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce166.imag, %complex_mul_libcall ]
  %t167 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i48 = load { float, float }*, { float, float }** %t167, align 8
  %arrayidx168 = getelementptr inbounds { float, float }, { float, float }* %i48, i64 3
  %arrayidx168.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx168, i32 0, i32 0
  %arrayidx168.real = load float, float* %arrayidx168.realp, align 4
  %arrayidx168.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx168, i32 0, i32 1
  %arrayidx168.imag = load float, float* %arrayidx168.imagp, align 4
  %t.realp169 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real = load float, float* %t.realp169, align 4
  %t.imagp170 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag = load float, float* %t.imagp170, align 4
  %mul_ac171 = fmul float %arrayidx168.real, %t.real
  %mul_bd172 = fmul float %arrayidx168.imag, %t.imag
  %mul_ad173 = fmul float %arrayidx168.real, %t.imag
  %mul_bc174 = fmul float %arrayidx168.imag, %t.real
  %mul_r175 = fsub float %mul_ac171, %mul_bd172
  %mul_i176 = fadd float %mul_ad173, %mul_bc174
  %isnan_cmp177 = fcmp uno float %mul_r175, %mul_r175
  br i1 %isnan_cmp177, label %complex_mul_imag_nan178, label %complex_mul_cont183, !prof !2

complex_mul_imag_nan178:                          ; preds = %complex_mul_cont
  %isnan_cmp179 = fcmp uno float %mul_i176, %mul_i176
  br i1 %isnan_cmp179, label %complex_mul_libcall180, label %complex_mul_cont183, !prof !2

complex_mul_libcall180:                           ; preds = %complex_mul_imag_nan178
  %call181 = call <2 x float> @__mulsc3(float %arrayidx168.real, float %arrayidx168.imag, float %t.real, float %t.imag) #9
  %i49 = bitcast { float, float }* %coerce182 to <2 x float>*
  store <2 x float> %call181, <2 x float>* %i49, align 4
  %coerce182.realp = getelementptr inbounds { float, float }, { float, float }* %coerce182, i32 0, i32 0
  %coerce182.real = load float, float* %coerce182.realp, align 4
  %coerce182.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce182, i32 0, i32 1
  %coerce182.imag = load float, float* %coerce182.imagp, align 4
  br label %complex_mul_cont183

complex_mul_cont183:                              ; preds = %complex_mul_libcall180, %complex_mul_imag_nan178, %complex_mul_cont
  %real_mul_phi184 = phi float [ %mul_r175, %complex_mul_cont ], [ %mul_r175, %complex_mul_imag_nan178 ], [ %coerce182.real, %complex_mul_libcall180 ]
  %imag_mul_phi185 = phi float [ %mul_i176, %complex_mul_cont ], [ %mul_i176, %complex_mul_imag_nan178 ], [ %coerce182.imag, %complex_mul_libcall180 ]
  %add.r = fadd float %real_mul_phi, %real_mul_phi184
  %add.i = fadd float %imag_mul_phi, %imag_mul_phi185
  %node186 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i50 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node186, align 8
  %idxprom187 = sext i32 %i.4 to i64
  %arrayidx188 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i50, i64 %idxprom187
  %amplitude189 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx188, i32 0, i32 0
  %amplitude189.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude189, i32 0, i32 0
  %amplitude189.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude189, i32 0, i32 1
  store float %add.r, float* %amplitude189.realp, align 8
  store float %add.i, float* %amplitude189.imagp, align 4
  br label %if.end238

if.else:                                          ; preds = %if.end157
  %t190 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i51 = load { float, float }*, { float, float }** %t190, align 8
  %arrayidx191 = getelementptr inbounds { float, float }, { float, float }* %i51, i64 0
  %arrayidx191.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx191, i32 0, i32 0
  %arrayidx191.real = load float, float* %arrayidx191.realp, align 4
  %arrayidx191.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx191, i32 0, i32 1
  %arrayidx191.imag = load float, float* %arrayidx191.imagp, align 4
  %t.realp192 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real193 = load float, float* %t.realp192, align 4
  %t.imagp194 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag195 = load float, float* %t.imagp194, align 4
  %mul_ac196 = fmul float %arrayidx191.real, %t.real193
  %mul_bd197 = fmul float %arrayidx191.imag, %t.imag195
  %mul_ad198 = fmul float %arrayidx191.real, %t.imag195
  %mul_bc199 = fmul float %arrayidx191.imag, %t.real193
  %mul_r200 = fsub float %mul_ac196, %mul_bd197
  %mul_i201 = fadd float %mul_ad198, %mul_bc199
  %isnan_cmp202 = fcmp uno float %mul_r200, %mul_r200
  br i1 %isnan_cmp202, label %complex_mul_imag_nan203, label %complex_mul_cont208, !prof !2

complex_mul_imag_nan203:                          ; preds = %if.else
  %isnan_cmp204 = fcmp uno float %mul_i201, %mul_i201
  br i1 %isnan_cmp204, label %complex_mul_libcall205, label %complex_mul_cont208, !prof !2

complex_mul_libcall205:                           ; preds = %complex_mul_imag_nan203
  %call206 = call <2 x float> @__mulsc3(float %arrayidx191.real, float %arrayidx191.imag, float %t.real193, float %t.imag195) #9
  %i52 = bitcast { float, float }* %coerce207 to <2 x float>*
  store <2 x float> %call206, <2 x float>* %i52, align 4
  %coerce207.realp = getelementptr inbounds { float, float }, { float, float }* %coerce207, i32 0, i32 0
  %coerce207.real = load float, float* %coerce207.realp, align 4
  %coerce207.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce207, i32 0, i32 1
  %coerce207.imag = load float, float* %coerce207.imagp, align 4
  br label %complex_mul_cont208

complex_mul_cont208:                              ; preds = %complex_mul_libcall205, %complex_mul_imag_nan203, %if.else
  %real_mul_phi209 = phi float [ %mul_r200, %if.else ], [ %mul_r200, %complex_mul_imag_nan203 ], [ %coerce207.real, %complex_mul_libcall205 ]
  %imag_mul_phi210 = phi float [ %mul_i201, %if.else ], [ %mul_i201, %complex_mul_imag_nan203 ], [ %coerce207.imag, %complex_mul_libcall205 ]
  %t211 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i53 = load { float, float }*, { float, float }** %t211, align 8
  %arrayidx212 = getelementptr inbounds { float, float }, { float, float }* %i53, i64 1
  %arrayidx212.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx212, i32 0, i32 0
  %arrayidx212.real = load float, float* %arrayidx212.realp, align 4
  %arrayidx212.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx212, i32 0, i32 1
  %arrayidx212.imag = load float, float* %arrayidx212.imagp, align 4
  %tnot.realp213 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real214 = load float, float* %tnot.realp213, align 4
  %tnot.imagp215 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag216 = load float, float* %tnot.imagp215, align 4
  %mul_ac217 = fmul float %arrayidx212.real, %tnot.real214
  %mul_bd218 = fmul float %arrayidx212.imag, %tnot.imag216
  %mul_ad219 = fmul float %arrayidx212.real, %tnot.imag216
  %mul_bc220 = fmul float %arrayidx212.imag, %tnot.real214
  %mul_r221 = fsub float %mul_ac217, %mul_bd218
  %mul_i222 = fadd float %mul_ad219, %mul_bc220
  %isnan_cmp223 = fcmp uno float %mul_r221, %mul_r221
  br i1 %isnan_cmp223, label %complex_mul_imag_nan224, label %complex_mul_cont229, !prof !2

complex_mul_imag_nan224:                          ; preds = %complex_mul_cont208
  %isnan_cmp225 = fcmp uno float %mul_i222, %mul_i222
  br i1 %isnan_cmp225, label %complex_mul_libcall226, label %complex_mul_cont229, !prof !2

complex_mul_libcall226:                           ; preds = %complex_mul_imag_nan224
  %call227 = call <2 x float> @__mulsc3(float %arrayidx212.real, float %arrayidx212.imag, float %tnot.real214, float %tnot.imag216) #9
  %i54 = bitcast { float, float }* %coerce228 to <2 x float>*
  store <2 x float> %call227, <2 x float>* %i54, align 4
  %coerce228.realp = getelementptr inbounds { float, float }, { float, float }* %coerce228, i32 0, i32 0
  %coerce228.real = load float, float* %coerce228.realp, align 4
  %coerce228.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce228, i32 0, i32 1
  %coerce228.imag = load float, float* %coerce228.imagp, align 4
  br label %complex_mul_cont229

complex_mul_cont229:                              ; preds = %complex_mul_libcall226, %complex_mul_imag_nan224, %complex_mul_cont208
  %real_mul_phi230 = phi float [ %mul_r221, %complex_mul_cont208 ], [ %mul_r221, %complex_mul_imag_nan224 ], [ %coerce228.real, %complex_mul_libcall226 ]
  %imag_mul_phi231 = phi float [ %mul_i222, %complex_mul_cont208 ], [ %mul_i222, %complex_mul_imag_nan224 ], [ %coerce228.imag, %complex_mul_libcall226 ]
  %add.r232 = fadd float %real_mul_phi209, %real_mul_phi230
  %add.i233 = fadd float %imag_mul_phi210, %imag_mul_phi231
  %node234 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i55 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node234, align 8
  %idxprom235 = sext i32 %i.4 to i64
  %arrayidx236 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i55, i64 %idxprom235
  %amplitude237 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx236, i32 0, i32 0
  %amplitude237.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude237, i32 0, i32 0
  %amplitude237.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude237, i32 0, i32 1
  store float %add.r232, float* %amplitude237.realp, align 8
  store float %add.i233, float* %amplitude237.imagp, align 4
  br label %if.end238

if.end238:                                        ; preds = %complex_mul_cont229, %complex_mul_cont183
  %cmp239 = icmp sge i32 %call143, 0
  br i1 %cmp239, label %if.then241, label %if.else342

if.then241:                                       ; preds = %if.end238
  %tobool242 = icmp ne i32 %conv133, 0
  br i1 %tobool242, label %if.then243, label %if.else292

if.then243:                                       ; preds = %if.then241
  %t244 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i56 = load { float, float }*, { float, float }** %t244, align 8
  %arrayidx245 = getelementptr inbounds { float, float }, { float, float }* %i56, i64 0
  %arrayidx245.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx245, i32 0, i32 0
  %arrayidx245.real = load float, float* %arrayidx245.realp, align 4
  %arrayidx245.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx245, i32 0, i32 1
  %arrayidx245.imag = load float, float* %arrayidx245.imagp, align 4
  %tnot.realp246 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real247 = load float, float* %tnot.realp246, align 4
  %tnot.imagp248 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag249 = load float, float* %tnot.imagp248, align 4
  %mul_ac250 = fmul float %arrayidx245.real, %tnot.real247
  %mul_bd251 = fmul float %arrayidx245.imag, %tnot.imag249
  %mul_ad252 = fmul float %arrayidx245.real, %tnot.imag249
  %mul_bc253 = fmul float %arrayidx245.imag, %tnot.real247
  %mul_r254 = fsub float %mul_ac250, %mul_bd251
  %mul_i255 = fadd float %mul_ad252, %mul_bc253
  %isnan_cmp256 = fcmp uno float %mul_r254, %mul_r254
  br i1 %isnan_cmp256, label %complex_mul_imag_nan257, label %complex_mul_cont262, !prof !2

complex_mul_imag_nan257:                          ; preds = %if.then243
  %isnan_cmp258 = fcmp uno float %mul_i255, %mul_i255
  br i1 %isnan_cmp258, label %complex_mul_libcall259, label %complex_mul_cont262, !prof !2

complex_mul_libcall259:                           ; preds = %complex_mul_imag_nan257
  %call260 = call <2 x float> @__mulsc3(float %arrayidx245.real, float %arrayidx245.imag, float %tnot.real247, float %tnot.imag249) #9
  %i57 = bitcast { float, float }* %coerce261 to <2 x float>*
  store <2 x float> %call260, <2 x float>* %i57, align 4
  %coerce261.realp = getelementptr inbounds { float, float }, { float, float }* %coerce261, i32 0, i32 0
  %coerce261.real = load float, float* %coerce261.realp, align 4
  %coerce261.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce261, i32 0, i32 1
  %coerce261.imag = load float, float* %coerce261.imagp, align 4
  br label %complex_mul_cont262

complex_mul_cont262:                              ; preds = %complex_mul_libcall259, %complex_mul_imag_nan257, %if.then243
  %real_mul_phi263 = phi float [ %mul_r254, %if.then243 ], [ %mul_r254, %complex_mul_imag_nan257 ], [ %coerce261.real, %complex_mul_libcall259 ]
  %imag_mul_phi264 = phi float [ %mul_i255, %if.then243 ], [ %mul_i255, %complex_mul_imag_nan257 ], [ %coerce261.imag, %complex_mul_libcall259 ]
  %t265 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i58 = load { float, float }*, { float, float }** %t265, align 8
  %arrayidx266 = getelementptr inbounds { float, float }, { float, float }* %i58, i64 1
  %arrayidx266.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx266, i32 0, i32 0
  %arrayidx266.real = load float, float* %arrayidx266.realp, align 4
  %arrayidx266.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx266, i32 0, i32 1
  %arrayidx266.imag = load float, float* %arrayidx266.imagp, align 4
  %t.realp267 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real268 = load float, float* %t.realp267, align 4
  %t.imagp269 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag270 = load float, float* %t.imagp269, align 4
  %mul_ac271 = fmul float %arrayidx266.real, %t.real268
  %mul_bd272 = fmul float %arrayidx266.imag, %t.imag270
  %mul_ad273 = fmul float %arrayidx266.real, %t.imag270
  %mul_bc274 = fmul float %arrayidx266.imag, %t.real268
  %mul_r275 = fsub float %mul_ac271, %mul_bd272
  %mul_i276 = fadd float %mul_ad273, %mul_bc274
  %isnan_cmp277 = fcmp uno float %mul_r275, %mul_r275
  br i1 %isnan_cmp277, label %complex_mul_imag_nan278, label %complex_mul_cont283, !prof !2

complex_mul_imag_nan278:                          ; preds = %complex_mul_cont262
  %isnan_cmp279 = fcmp uno float %mul_i276, %mul_i276
  br i1 %isnan_cmp279, label %complex_mul_libcall280, label %complex_mul_cont283, !prof !2

complex_mul_libcall280:                           ; preds = %complex_mul_imag_nan278
  %call281 = call <2 x float> @__mulsc3(float %arrayidx266.real, float %arrayidx266.imag, float %t.real268, float %t.imag270) #9
  %i59 = bitcast { float, float }* %coerce282 to <2 x float>*
  store <2 x float> %call281, <2 x float>* %i59, align 4
  %coerce282.realp = getelementptr inbounds { float, float }, { float, float }* %coerce282, i32 0, i32 0
  %coerce282.real = load float, float* %coerce282.realp, align 4
  %coerce282.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce282, i32 0, i32 1
  %coerce282.imag = load float, float* %coerce282.imagp, align 4
  br label %complex_mul_cont283

complex_mul_cont283:                              ; preds = %complex_mul_libcall280, %complex_mul_imag_nan278, %complex_mul_cont262
  %real_mul_phi284 = phi float [ %mul_r275, %complex_mul_cont262 ], [ %mul_r275, %complex_mul_imag_nan278 ], [ %coerce282.real, %complex_mul_libcall280 ]
  %imag_mul_phi285 = phi float [ %mul_i276, %complex_mul_cont262 ], [ %mul_i276, %complex_mul_imag_nan278 ], [ %coerce282.imag, %complex_mul_libcall280 ]
  %add.r286 = fadd float %real_mul_phi263, %real_mul_phi284
  %add.i287 = fadd float %imag_mul_phi264, %imag_mul_phi285
  %node288 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i60 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node288, align 8
  %idxprom289 = sext i32 %call143 to i64
  %arrayidx290 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i60, i64 %idxprom289
  %amplitude291 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx290, i32 0, i32 0
  %amplitude291.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude291, i32 0, i32 0
  %amplitude291.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude291, i32 0, i32 1
  store float %add.r286, float* %amplitude291.realp, align 8
  store float %add.i287, float* %amplitude291.imagp, align 4
  br label %if.end341

if.else292:                                       ; preds = %if.then241
  %t293 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i61 = load { float, float }*, { float, float }** %t293, align 8
  %arrayidx294 = getelementptr inbounds { float, float }, { float, float }* %i61, i64 2
  %arrayidx294.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx294, i32 0, i32 0
  %arrayidx294.real = load float, float* %arrayidx294.realp, align 4
  %arrayidx294.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx294, i32 0, i32 1
  %arrayidx294.imag = load float, float* %arrayidx294.imagp, align 4
  %t.realp295 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real296 = load float, float* %t.realp295, align 4
  %t.imagp297 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag298 = load float, float* %t.imagp297, align 4
  %mul_ac299 = fmul float %arrayidx294.real, %t.real296
  %mul_bd300 = fmul float %arrayidx294.imag, %t.imag298
  %mul_ad301 = fmul float %arrayidx294.real, %t.imag298
  %mul_bc302 = fmul float %arrayidx294.imag, %t.real296
  %mul_r303 = fsub float %mul_ac299, %mul_bd300
  %mul_i304 = fadd float %mul_ad301, %mul_bc302
  %isnan_cmp305 = fcmp uno float %mul_r303, %mul_r303
  br i1 %isnan_cmp305, label %complex_mul_imag_nan306, label %complex_mul_cont311, !prof !2

complex_mul_imag_nan306:                          ; preds = %if.else292
  %isnan_cmp307 = fcmp uno float %mul_i304, %mul_i304
  br i1 %isnan_cmp307, label %complex_mul_libcall308, label %complex_mul_cont311, !prof !2

complex_mul_libcall308:                           ; preds = %complex_mul_imag_nan306
  %call309 = call <2 x float> @__mulsc3(float %arrayidx294.real, float %arrayidx294.imag, float %t.real296, float %t.imag298) #9
  %i62 = bitcast { float, float }* %coerce310 to <2 x float>*
  store <2 x float> %call309, <2 x float>* %i62, align 4
  %coerce310.realp = getelementptr inbounds { float, float }, { float, float }* %coerce310, i32 0, i32 0
  %coerce310.real = load float, float* %coerce310.realp, align 4
  %coerce310.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce310, i32 0, i32 1
  %coerce310.imag = load float, float* %coerce310.imagp, align 4
  br label %complex_mul_cont311

complex_mul_cont311:                              ; preds = %complex_mul_libcall308, %complex_mul_imag_nan306, %if.else292
  %real_mul_phi312 = phi float [ %mul_r303, %if.else292 ], [ %mul_r303, %complex_mul_imag_nan306 ], [ %coerce310.real, %complex_mul_libcall308 ]
  %imag_mul_phi313 = phi float [ %mul_i304, %if.else292 ], [ %mul_i304, %complex_mul_imag_nan306 ], [ %coerce310.imag, %complex_mul_libcall308 ]
  %t314 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i63 = load { float, float }*, { float, float }** %t314, align 8
  %arrayidx315 = getelementptr inbounds { float, float }, { float, float }* %i63, i64 3
  %arrayidx315.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx315, i32 0, i32 0
  %arrayidx315.real = load float, float* %arrayidx315.realp, align 4
  %arrayidx315.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx315, i32 0, i32 1
  %arrayidx315.imag = load float, float* %arrayidx315.imagp, align 4
  %tnot.realp316 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real317 = load float, float* %tnot.realp316, align 4
  %tnot.imagp318 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag319 = load float, float* %tnot.imagp318, align 4
  %mul_ac320 = fmul float %arrayidx315.real, %tnot.real317
  %mul_bd321 = fmul float %arrayidx315.imag, %tnot.imag319
  %mul_ad322 = fmul float %arrayidx315.real, %tnot.imag319
  %mul_bc323 = fmul float %arrayidx315.imag, %tnot.real317
  %mul_r324 = fsub float %mul_ac320, %mul_bd321
  %mul_i325 = fadd float %mul_ad322, %mul_bc323
  %isnan_cmp326 = fcmp uno float %mul_r324, %mul_r324
  br i1 %isnan_cmp326, label %complex_mul_imag_nan327, label %complex_mul_cont332, !prof !2

complex_mul_imag_nan327:                          ; preds = %complex_mul_cont311
  %isnan_cmp328 = fcmp uno float %mul_i325, %mul_i325
  br i1 %isnan_cmp328, label %complex_mul_libcall329, label %complex_mul_cont332, !prof !2

complex_mul_libcall329:                           ; preds = %complex_mul_imag_nan327
  %call330 = call <2 x float> @__mulsc3(float %arrayidx315.real, float %arrayidx315.imag, float %tnot.real317, float %tnot.imag319) #9
  %i64 = bitcast { float, float }* %coerce331 to <2 x float>*
  store <2 x float> %call330, <2 x float>* %i64, align 4
  %coerce331.realp = getelementptr inbounds { float, float }, { float, float }* %coerce331, i32 0, i32 0
  %coerce331.real = load float, float* %coerce331.realp, align 4
  %coerce331.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce331, i32 0, i32 1
  %coerce331.imag = load float, float* %coerce331.imagp, align 4
  br label %complex_mul_cont332

complex_mul_cont332:                              ; preds = %complex_mul_libcall329, %complex_mul_imag_nan327, %complex_mul_cont311
  %real_mul_phi333 = phi float [ %mul_r324, %complex_mul_cont311 ], [ %mul_r324, %complex_mul_imag_nan327 ], [ %coerce331.real, %complex_mul_libcall329 ]
  %imag_mul_phi334 = phi float [ %mul_i325, %complex_mul_cont311 ], [ %mul_i325, %complex_mul_imag_nan327 ], [ %coerce331.imag, %complex_mul_libcall329 ]
  %add.r335 = fadd float %real_mul_phi312, %real_mul_phi333
  %add.i336 = fadd float %imag_mul_phi313, %imag_mul_phi334
  %node337 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i65 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node337, align 8
  %idxprom338 = sext i32 %call143 to i64
  %arrayidx339 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i65, i64 %idxprom338
  %amplitude340 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx339, i32 0, i32 0
  %amplitude340.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude340, i32 0, i32 0
  %amplitude340.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude340, i32 0, i32 1
  store float %add.r335, float* %amplitude340.realp, align 8
  store float %add.i336, float* %amplitude340.imagp, align 4
  br label %if.end341

if.end341:                                        ; preds = %complex_mul_cont332, %complex_mul_cont283
  br label %if.end431

if.else342:                                       ; preds = %if.end238
  %t343 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i66 = load { float, float }*, { float, float }** %t343, align 8
  %arrayidx344 = getelementptr inbounds { float, float }, { float, float }* %i66, i64 1
  %arrayidx344.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx344, i32 0, i32 0
  %arrayidx344.real = load float, float* %arrayidx344.realp, align 4
  %arrayidx344.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx344, i32 0, i32 1
  %arrayidx344.imag = load float, float* %arrayidx344.imagp, align 4
  %coerce345.realp = getelementptr inbounds { float, float }, { float, float }* %coerce345, i32 0, i32 0
  %coerce345.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce345, i32 0, i32 1
  store float %arrayidx344.real, float* %coerce345.realp, align 4
  store float %arrayidx344.imag, float* %coerce345.imagp, align 4
  %i67 = bitcast { float, float }* %coerce345 to <2 x float>*
  %i68 = load <2 x float>, <2 x float>* %i67, align 4
  %call346 = call float @quantum_prob_inline.5(<2 x float> %i68)
  %conv347 = fpext float %call346 to double
  %cmp348 = fcmp olt double %conv347, 1.000000e-09
  br i1 %cmp348, label %land.lhs.true350, label %if.end353

land.lhs.true350:                                 ; preds = %if.else342
  %tobool351 = icmp ne i32 %conv133, 0
  br i1 %tobool351, label %if.then352, label %if.end353

if.then352:                                       ; preds = %land.lhs.true350
  br label %for.end441

if.end353:                                        ; preds = %land.lhs.true350, %if.else342
  %t354 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i69 = load { float, float }*, { float, float }** %t354, align 8
  %arrayidx355 = getelementptr inbounds { float, float }, { float, float }* %i69, i64 2
  %arrayidx355.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx355, i32 0, i32 0
  %arrayidx355.real = load float, float* %arrayidx355.realp, align 4
  %arrayidx355.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx355, i32 0, i32 1
  %arrayidx355.imag = load float, float* %arrayidx355.imagp, align 4
  %coerce356.realp = getelementptr inbounds { float, float }, { float, float }* %coerce356, i32 0, i32 0
  %coerce356.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce356, i32 0, i32 1
  store float %arrayidx355.real, float* %coerce356.realp, align 4
  store float %arrayidx355.imag, float* %coerce356.imagp, align 4
  %i70 = bitcast { float, float }* %coerce356 to <2 x float>*
  %i71 = load <2 x float>, <2 x float>* %i70, align 4
  %call357 = call float @quantum_prob_inline.5(<2 x float> %i71)
  %conv358 = fpext float %call357 to double
  %cmp359 = fcmp olt double %conv358, 1.000000e-09
  br i1 %cmp359, label %land.lhs.true361, label %if.end364

land.lhs.true361:                                 ; preds = %if.end353
  %tobool362 = icmp ne i32 %conv133, 0
  br i1 %tobool362, label %if.end364, label %if.then363

if.then363:                                       ; preds = %land.lhs.true361
  br label %for.end441

if.end364:                                        ; preds = %land.lhs.true361, %if.end353
  %node365 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i72 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node365, align 8
  %idxprom366 = sext i32 %i.4 to i64
  %arrayidx367 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i72, i64 %idxprom366
  %state368 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx367, i32 0, i32 1
  %i73 = load i64, i64* %state368, align 8
  %sh_prom369 = zext i32 %target to i64
  %shl370 = shl i64 1, %sh_prom369
  %xor371 = xor i64 %i73, %shl370
  %node372 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i74 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node372, align 8
  %idxprom373 = sext i32 %k.0 to i64
  %arrayidx374 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i74, i64 %idxprom373
  %state375 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx374, i32 0, i32 1
  store i64 %xor371, i64* %state375, align 8
  %tobool376 = icmp ne i32 %conv133, 0
  br i1 %tobool376, label %if.then377, label %if.else403

if.then377:                                       ; preds = %if.end364
  %t378 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i75 = load { float, float }*, { float, float }** %t378, align 8
  %arrayidx379 = getelementptr inbounds { float, float }, { float, float }* %i75, i64 1
  %arrayidx379.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx379, i32 0, i32 0
  %arrayidx379.real = load float, float* %arrayidx379.realp, align 4
  %arrayidx379.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx379, i32 0, i32 1
  %arrayidx379.imag = load float, float* %arrayidx379.imagp, align 4
  %t.realp380 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real381 = load float, float* %t.realp380, align 4
  %t.imagp382 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag383 = load float, float* %t.imagp382, align 4
  %mul_ac384 = fmul float %arrayidx379.real, %t.real381
  %mul_bd385 = fmul float %arrayidx379.imag, %t.imag383
  %mul_ad386 = fmul float %arrayidx379.real, %t.imag383
  %mul_bc387 = fmul float %arrayidx379.imag, %t.real381
  %mul_r388 = fsub float %mul_ac384, %mul_bd385
  %mul_i389 = fadd float %mul_ad386, %mul_bc387
  %isnan_cmp390 = fcmp uno float %mul_r388, %mul_r388
  br i1 %isnan_cmp390, label %complex_mul_imag_nan391, label %complex_mul_cont396, !prof !2

complex_mul_imag_nan391:                          ; preds = %if.then377
  %isnan_cmp392 = fcmp uno float %mul_i389, %mul_i389
  br i1 %isnan_cmp392, label %complex_mul_libcall393, label %complex_mul_cont396, !prof !2

complex_mul_libcall393:                           ; preds = %complex_mul_imag_nan391
  %call394 = call <2 x float> @__mulsc3(float %arrayidx379.real, float %arrayidx379.imag, float %t.real381, float %t.imag383) #9
  %i76 = bitcast { float, float }* %coerce395 to <2 x float>*
  store <2 x float> %call394, <2 x float>* %i76, align 4
  %coerce395.realp = getelementptr inbounds { float, float }, { float, float }* %coerce395, i32 0, i32 0
  %coerce395.real = load float, float* %coerce395.realp, align 4
  %coerce395.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce395, i32 0, i32 1
  %coerce395.imag = load float, float* %coerce395.imagp, align 4
  br label %complex_mul_cont396

complex_mul_cont396:                              ; preds = %complex_mul_libcall393, %complex_mul_imag_nan391, %if.then377
  %real_mul_phi397 = phi float [ %mul_r388, %if.then377 ], [ %mul_r388, %complex_mul_imag_nan391 ], [ %coerce395.real, %complex_mul_libcall393 ]
  %imag_mul_phi398 = phi float [ %mul_i389, %if.then377 ], [ %mul_i389, %complex_mul_imag_nan391 ], [ %coerce395.imag, %complex_mul_libcall393 ]
  %node399 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i77 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node399, align 8
  %idxprom400 = sext i32 %k.0 to i64
  %arrayidx401 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i77, i64 %idxprom400
  %amplitude402 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx401, i32 0, i32 0
  %amplitude402.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude402, i32 0, i32 0
  %amplitude402.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude402, i32 0, i32 1
  store float %real_mul_phi397, float* %amplitude402.realp, align 8
  store float %imag_mul_phi398, float* %amplitude402.imagp, align 4
  br label %if.end429

if.else403:                                       ; preds = %if.end364
  %t404 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i78 = load { float, float }*, { float, float }** %t404, align 8
  %arrayidx405 = getelementptr inbounds { float, float }, { float, float }* %i78, i64 2
  %arrayidx405.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx405, i32 0, i32 0
  %arrayidx405.real = load float, float* %arrayidx405.realp, align 4
  %arrayidx405.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx405, i32 0, i32 1
  %arrayidx405.imag = load float, float* %arrayidx405.imagp, align 4
  %t.realp406 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real407 = load float, float* %t.realp406, align 4
  %t.imagp408 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag409 = load float, float* %t.imagp408, align 4
  %mul_ac410 = fmul float %arrayidx405.real, %t.real407
  %mul_bd411 = fmul float %arrayidx405.imag, %t.imag409
  %mul_ad412 = fmul float %arrayidx405.real, %t.imag409
  %mul_bc413 = fmul float %arrayidx405.imag, %t.real407
  %mul_r414 = fsub float %mul_ac410, %mul_bd411
  %mul_i415 = fadd float %mul_ad412, %mul_bc413
  %isnan_cmp416 = fcmp uno float %mul_r414, %mul_r414
  br i1 %isnan_cmp416, label %complex_mul_imag_nan417, label %complex_mul_cont422, !prof !2

complex_mul_imag_nan417:                          ; preds = %if.else403
  %isnan_cmp418 = fcmp uno float %mul_i415, %mul_i415
  br i1 %isnan_cmp418, label %complex_mul_libcall419, label %complex_mul_cont422, !prof !2

complex_mul_libcall419:                           ; preds = %complex_mul_imag_nan417
  %call420 = call <2 x float> @__mulsc3(float %arrayidx405.real, float %arrayidx405.imag, float %t.real407, float %t.imag409) #9
  %i79 = bitcast { float, float }* %coerce421 to <2 x float>*
  store <2 x float> %call420, <2 x float>* %i79, align 4
  %coerce421.realp = getelementptr inbounds { float, float }, { float, float }* %coerce421, i32 0, i32 0
  %coerce421.real = load float, float* %coerce421.realp, align 4
  %coerce421.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce421, i32 0, i32 1
  %coerce421.imag = load float, float* %coerce421.imagp, align 4
  br label %complex_mul_cont422

complex_mul_cont422:                              ; preds = %complex_mul_libcall419, %complex_mul_imag_nan417, %if.else403
  %real_mul_phi423 = phi float [ %mul_r414, %if.else403 ], [ %mul_r414, %complex_mul_imag_nan417 ], [ %coerce421.real, %complex_mul_libcall419 ]
  %imag_mul_phi424 = phi float [ %mul_i415, %if.else403 ], [ %mul_i415, %complex_mul_imag_nan417 ], [ %coerce421.imag, %complex_mul_libcall419 ]
  %node425 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i80 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node425, align 8
  %idxprom426 = sext i32 %k.0 to i64
  %arrayidx427 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i80, i64 %idxprom426
  %amplitude428 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx427, i32 0, i32 0
  %amplitude428.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude428, i32 0, i32 0
  %amplitude428.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude428, i32 0, i32 1
  store float %real_mul_phi423, float* %amplitude428.realp, align 8
  store float %imag_mul_phi424, float* %amplitude428.imagp, align 4
  br label %if.end429

if.end429:                                        ; preds = %complex_mul_cont422, %complex_mul_cont396
  %inc430 = add nsw i32 %k.0, 1
  br label %if.end431

if.end431:                                        ; preds = %if.end429, %if.end341
  %k.1 = phi i32 [ %k.0, %if.end341 ], [ %inc430, %if.end429 ]
  %cmp432 = icmp sge i32 %call143, 0
  br i1 %cmp432, label %if.then434, label %if.end437

if.then434:                                       ; preds = %if.end431
  %idxprom435 = sext i32 %call143 to i64
  %arrayidx436 = getelementptr inbounds i8, i8* %call96, i64 %idxprom435
  store i8 1, i8* %arrayidx436, align 1
  br label %if.end437

if.end437:                                        ; preds = %if.then434, %if.end431
  br label %if.end438

if.end438:                                        ; preds = %if.end437, %for.body121
  %k.2 = phi i32 [ %k.0, %for.body121 ], [ %k.1, %if.end437 ]
  br label %for.inc439

for.inc439:                                       ; preds = %if.end438
  %inc440 = add nsw i32 %i.4, 1
  br label %for.cond117

for.end441:                                       ; preds = %if.then363, %if.then352, %for.cond117
  %size442 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i81 = load i32, i32* %size442, align 4
  %add443 = add nsw i32 %i81, %addsize.0
  store i32 %add443, i32* %size442, align 4
  call void @free(i8* %call96) #9
  %size444 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i82 = load i32, i32* %size444, align 4
  %sub = sub nsw i32 0, %i82
  %conv445 = sext i32 %sub to i64
  %mul446 = mul i64 %conv445, 1
  %call447 = call i64 @quantum_memman(i64 %mul446)
  br label %for.cond448

for.cond448:                                      ; preds = %for.inc487, %for.end441
  %j.0 = phi i32 [ 0, %for.end441 ], [ %j.1, %for.inc487 ]
  %i.5 = phi i32 [ 0, %for.end441 ], [ %inc488, %for.inc487 ]
  %decsize.0 = phi i32 [ 0, %for.end441 ], [ %decsize.1, %for.inc487 ]
  %size449 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i83 = load i32, i32* %size449, align 4
  %cmp450 = icmp slt i32 %i.5, %i83
  br i1 %cmp450, label %for.body452, label %for.end489

for.body452:                                      ; preds = %for.cond448
  %node453 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i84 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node453, align 8
  %idxprom454 = sext i32 %i.5 to i64
  %arrayidx455 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i84, i64 %idxprom454
  %amplitude456 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx455, i32 0, i32 0
  %amplitude456.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude456, i32 0, i32 0
  %amplitude456.real = load float, float* %amplitude456.realp, align 8
  %amplitude456.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude456, i32 0, i32 1
  %amplitude456.imag = load float, float* %amplitude456.imagp, align 4
  %coerce457.realp = getelementptr inbounds { float, float }, { float, float }* %coerce457, i32 0, i32 0
  %coerce457.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce457, i32 0, i32 1
  store float %amplitude456.real, float* %coerce457.realp, align 4
  store float %amplitude456.imag, float* %coerce457.imagp, align 4
  %i85 = bitcast { float, float }* %coerce457 to <2 x float>*
  %i86 = load <2 x float>, <2 x float>* %i85, align 4
  %call458 = call float @quantum_prob_inline.5(<2 x float> %i86)
  %cmp459 = fcmp olt float %call458, %conv116
  br i1 %cmp459, label %if.then461, label %if.else464

if.then461:                                       ; preds = %for.body452
  %inc462 = add nsw i32 %j.0, 1
  %inc463 = add nsw i32 %decsize.0, 1
  br label %if.end486

if.else464:                                       ; preds = %for.body452
  %tobool465 = icmp ne i32 %j.0, 0
  br i1 %tobool465, label %if.then466, label %if.end485

if.then466:                                       ; preds = %if.else464
  %node467 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i87 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node467, align 8
  %idxprom468 = sext i32 %i.5 to i64
  %arrayidx469 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i87, i64 %idxprom468
  %state470 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx469, i32 0, i32 1
  %i88 = load i64, i64* %state470, align 8
  %node471 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i89 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node471, align 8
  %sub472 = sub nsw i32 %i.5, %j.0
  %idxprom473 = sext i32 %sub472 to i64
  %arrayidx474 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i89, i64 %idxprom473
  %state475 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx474, i32 0, i32 1
  store i64 %i88, i64* %state475, align 8
  %node476 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i90 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node476, align 8
  %idxprom477 = sext i32 %i.5 to i64
  %arrayidx478 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i90, i64 %idxprom477
  %amplitude479 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx478, i32 0, i32 0
  %amplitude479.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude479, i32 0, i32 0
  %amplitude479.real = load float, float* %amplitude479.realp, align 8
  %amplitude479.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude479, i32 0, i32 1
  %amplitude479.imag = load float, float* %amplitude479.imagp, align 4
  %node480 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i91 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node480, align 8
  %sub481 = sub nsw i32 %i.5, %j.0
  %idxprom482 = sext i32 %sub481 to i64
  %arrayidx483 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i91, i64 %idxprom482
  %amplitude484 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx483, i32 0, i32 0
  %amplitude484.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude484, i32 0, i32 0
  %amplitude484.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude484, i32 0, i32 1
  store float %amplitude479.real, float* %amplitude484.realp, align 8
  store float %amplitude479.imag, float* %amplitude484.imagp, align 4
  br label %if.end485

if.end485:                                        ; preds = %if.then466, %if.else464
  br label %if.end486

if.end486:                                        ; preds = %if.end485, %if.then461
  %j.1 = phi i32 [ %inc462, %if.then461 ], [ %j.0, %if.end485 ]
  %decsize.1 = phi i32 [ %inc463, %if.then461 ], [ %decsize.0, %if.end485 ]
  br label %for.inc487

for.inc487:                                       ; preds = %if.end486
  %inc488 = add nsw i32 %i.5, 1
  br label %for.cond448

for.end489:                                       ; preds = %for.cond448
  %tobool490 = icmp ne i32 %decsize.0, 0
  br i1 %tobool490, label %if.then491, label %if.end511

if.then491:                                       ; preds = %for.end489
  %size492 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i92 = load i32, i32* %size492, align 4
  %sub493 = sub nsw i32 %i92, %decsize.0
  store i32 %sub493, i32* %size492, align 4
  %node494 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i93 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node494, align 8
  %i94 = bitcast %struct.quantum_reg_node_struct* %i93 to i8*
  %size495 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i95 = load i32, i32* %size495, align 4
  %conv496 = sext i32 %i95 to i64
  %mul497 = mul i64 %conv496, 16
  %call498 = call i8* @realloc(i8* %i94, i64 %mul497) #9
  %i96 = bitcast i8* %call498 to %struct.quantum_reg_node_struct*
  %node499 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i96, %struct.quantum_reg_node_struct** %node499, align 8
  %node500 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i97 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node500, align 8
  %tobool501 = icmp ne %struct.quantum_reg_node_struct* %i97, null
  br i1 %tobool501, label %if.end506, label %if.then502

if.then502:                                       ; preds = %if.then491
  %size503 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i98 = load i32, i32* %size503, align 4
  %add504 = add nsw i32 %i98, %addsize.0
  %call505 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.2, i64 0, i64 0), i32 %add504)
  call void @exit(i32 1) #10
  unreachable

if.end506:                                        ; preds = %if.then491
  %sub507 = sub nsw i32 0, %decsize.0
  %conv508 = sext i32 %sub507 to i64
  %mul509 = mul i64 %conv508, 16
  %call510 = call i64 @quantum_memman(i64 %mul509)
  br label %if.end511

if.end511:                                        ; preds = %if.end506, %for.end489
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal void @quantum_add_hash(i64 %a, i32 %pos, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i = load i32, i32* %hashw, align 8
  %call = call i32 @quantum_hash64(i64 %a, i32 %i)
  br label %while.cond

while.cond:                                       ; preds = %if.end, %entry
  %i.0 = phi i32 [ %call, %entry ], [ %i.1, %if.end ]
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i1 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %idxprom
  %i2 = load i32, i32* %arrayidx, align 4
  %tobool = icmp ne i32 %i2, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %inc = add nsw i32 %i.0, 1
  %hashw1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i3 = load i32, i32* %hashw1, align 8
  %shl = shl i32 1, %i3
  %cmp = icmp eq i32 %inc, %shl
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %while.body
  br label %if.end

if.end:                                           ; preds = %if.then, %while.body
  %i.1 = phi i32 [ 0, %if.then ], [ %inc, %while.body ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %add = add nsw i32 %pos, 1
  %hash2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i4 = load i32*, i32** %hash2, align 8
  %idxprom3 = sext i32 %i.0 to i64
  %arrayidx4 = getelementptr inbounds i32, i32* %i4, i64 %idxprom3
  store i32 %add, i32* %arrayidx4, align 4
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal i32 @quantum_get_state(i64 %a, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #0 {
entry:
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i = load i32, i32* %hashw, align 8
  %call = call i32 @quantum_hash64(i64 %a, i32 %i)
  br label %while.cond

while.cond:                                       ; preds = %if.end13, %entry
  %i.0 = phi i32 [ %call, %entry ], [ %i.1, %if.end13 ]
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i1 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %idxprom
  %i2 = load i32, i32* %arrayidx, align 4
  %tobool = icmp ne i32 %i2, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %hash1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i4 = load i32*, i32** %hash1, align 8
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds i32, i32* %i4, i64 %idxprom2
  %i5 = load i32, i32* %arrayidx3, align 4
  %sub = sub nsw i32 %i5, 1
  %idxprom4 = sext i32 %sub to i64
  %arrayidx5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom4
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx5, i32 0, i32 1
  %i6 = load i64, i64* %state, align 8
  %cmp = icmp eq i64 %i6, %a
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %while.body
  %hash6 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i7 = load i32*, i32** %hash6, align 8
  %idxprom7 = sext i32 %i.0 to i64
  %arrayidx8 = getelementptr inbounds i32, i32* %i7, i64 %idxprom7
  %i8 = load i32, i32* %arrayidx8, align 4
  %sub9 = sub nsw i32 %i8, 1
  br label %return

if.end:                                           ; preds = %while.body
  %inc = add nsw i32 %i.0, 1
  %hashw10 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i9 = load i32, i32* %hashw10, align 8
  %shl = shl i32 1, %i9
  %cmp11 = icmp eq i32 %inc, %shl
  br i1 %cmp11, label %if.then12, label %if.end13

if.then12:                                        ; preds = %if.end
  br label %if.end13

if.end13:                                         ; preds = %if.then12, %if.end
  %i.1 = phi i32 [ 0, %if.then12 ], [ %inc, %if.end ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  br label %return

return:                                           ; preds = %while.end, %if.then
  %retval.0 = phi i32 [ %sub9, %if.then ], [ -1, %while.end ]
  ret i32 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_prob_inline.5(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce5 = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %a.realp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real = load float, float* %a.realp, align 4
  %a.imagp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag = load float, float* %a.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %a.real, float* %coerce.realp, align 4
  store float %a.imag, float* %coerce.imagp, align 4
  %i1 = bitcast { float, float }* %coerce to <2 x float>*
  %i2 = load <2 x float>, <2 x float>* %i1, align 4
  %call = call float @quantum_real.6(<2 x float> %i2)
  %a.realp1 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real2 = load float, float* %a.realp1, align 4
  %a.imagp3 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag4 = load float, float* %a.imagp3, align 4
  %coerce5.realp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 0
  %coerce5.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 1
  store float %a.real2, float* %coerce5.realp, align 4
  store float %a.imag4, float* %coerce5.imagp, align 4
  %i3 = bitcast { float, float }* %coerce5 to <2 x float>*
  %i4 = load <2 x float>, <2 x float>* %i3, align 4
  %call6 = call float @quantum_imag.7(<2 x float> %i4)
  %mul = fmul float %call, %call
  %mul7 = fmul float %call6, %call6
  %add = fadd float %mul, %mul7
  ret float %add
}

; Function Attrs: nounwind
declare dso_local i8* @realloc(i8*, i64) #3

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_real.6(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 0
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_imag.7(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 1
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal i32 @quantum_hash64(i64 %key, i32 %width) #0 {
entry:
  %and = and i64 %key, 4294967295
  %shr = lshr i64 %key, 32
  %xor = xor i64 %and, %shr
  %conv = trunc i64 %xor to i32
  %conv1 = zext i32 %conv to i64
  %mul = mul i64 %conv1, 2654404609
  %conv2 = trunc i64 %mul to i32
  %sub = sub nsw i32 32, %width
  %shr3 = lshr i32 %conv2, %sub
  ret i32 %shr3
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_gate2(i32 %control, i32 %target, i64 %m.coerce0, { float, float }* %m.coerce1, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %m = alloca %struct.quantum_matrix_struct, align 8
  %t = alloca { float, float }, align 4
  %tnot = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce175 = alloca { float, float }, align 4
  %coerce200 = alloca { float, float }, align 4
  %coerce221 = alloca { float, float }, align 4
  %coerce254 = alloca { float, float }, align 4
  %coerce275 = alloca { float, float }, align 4
  %coerce303 = alloca { float, float }, align 4
  %coerce324 = alloca { float, float }, align 4
  %coerce385 = alloca { float, float }, align 4
  %coerce411 = alloca { float, float }, align 4
  %coerce447 = alloca { float, float }, align 4
  %i = bitcast %struct.quantum_matrix_struct* %m to { i64, { float, float }* }*
  %i1 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 0
  store i64 %m.coerce0, i64* %i1, align 8
  %i2 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 1
  store { float, float }* %m.coerce1, { float, float }** %i2, align 8
  %tnot.realp = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.imagp = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  store float 0.000000e+00, float* %tnot.realp, align 4
  store float 0.000000e+00, float* %tnot.imagp, align 4
  %cols = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i3 = load i32, i32* %cols, align 4
  %cmp = icmp ne i32 %i3, 4
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %rows = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i4 = load i32, i32* %rows, align 8
  %cmp1 = icmp ne i32 %i4, 4
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.4, i64 0, i64 0))
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %lor.lhs.false
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i5 = load i32, i32* %hashw, align 8
  %shl = shl i32 1, %i5
  %cmp2 = icmp slt i32 %i.0, %shl
  br i1 %cmp2, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i6 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i6, i64 %idxprom
  store i32 0, i32* %arrayidx, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond3

for.cond3:                                        ; preds = %for.inc8, %for.end
  %i.1 = phi i32 [ 0, %for.end ], [ %inc9, %for.inc8 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i7 = load i32, i32* %size, align 4
  %cmp4 = icmp slt i32 %i.1, %i7
  br i1 %cmp4, label %for.body5, label %for.end10

for.body5:                                        ; preds = %for.cond3
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom6 = sext i32 %i.1 to i64
  %arrayidx7 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i8, i64 %idxprom6
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx7, i32 0, i32 1
  %i9 = load i64, i64* %state, align 8
  call void @quantum_add_hash(i64 %i9, i32 %i.1, %struct.quantum_reg_struct* %reg)
  br label %for.inc8

for.inc8:                                         ; preds = %for.body5
  %inc9 = add nsw i32 %i.1, 1
  br label %for.cond3

for.end10:                                        ; preds = %for.cond3
  br label %for.cond11

for.cond11:                                       ; preds = %for.inc52, %for.end10
  %i.2 = phi i32 [ 0, %for.end10 ], [ %inc53, %for.inc52 ]
  %addsize.0 = phi i32 [ 0, %for.end10 ], [ %addsize.3, %for.inc52 ]
  %size12 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i10 = load i32, i32* %size12, align 4
  %cmp13 = icmp slt i32 %i.2, %i10
  br i1 %cmp13, label %for.body14, label %for.end54

for.body14:                                       ; preds = %for.cond11
  %node15 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i11 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node15, align 8
  %idxprom16 = sext i32 %i.2 to i64
  %arrayidx17 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i11, i64 %idxprom16
  %state18 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx17, i32 0, i32 1
  %i12 = load i64, i64* %state18, align 8
  %sh_prom = zext i32 %target to i64
  %shl19 = shl i64 1, %sh_prom
  %xor = xor i64 %i12, %shl19
  %call20 = call i32 @quantum_get_state(i64 %xor, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg)
  %cmp21 = icmp eq i32 %call20, -1
  br i1 %cmp21, label %if.then22, label %if.end51

if.then22:                                        ; preds = %for.body14
  %t23 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i13 = load { float, float }*, { float, float }** %t23, align 8
  %arrayidx24 = getelementptr inbounds { float, float }, { float, float }* %i13, i64 1
  %arrayidx24.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx24, i32 0, i32 0
  %arrayidx24.real = load float, float* %arrayidx24.realp, align 4
  %arrayidx24.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx24, i32 0, i32 1
  %arrayidx24.imag = load float, float* %arrayidx24.imagp, align 4
  %cmp.r = fcmp une float %arrayidx24.real, 0.000000e+00
  %cmp.i = fcmp une float %arrayidx24.imag, 0.000000e+00
  %or.ri = or i1 %cmp.r, %cmp.i
  br i1 %or.ri, label %land.lhs.true, label %if.end33

land.lhs.true:                                    ; preds = %if.then22
  %node25 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i14 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node25, align 8
  %idxprom26 = sext i32 %i.2 to i64
  %arrayidx27 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i14, i64 %idxprom26
  %state28 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx27, i32 0, i32 1
  %i15 = load i64, i64* %state28, align 8
  %sh_prom29 = zext i32 %target to i64
  %shl30 = shl i64 1, %sh_prom29
  %and = and i64 %i15, %shl30
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %if.then31, label %if.end33

if.then31:                                        ; preds = %land.lhs.true
  %inc32 = add nsw i32 %addsize.0, 1
  br label %if.end33

if.end33:                                         ; preds = %if.then31, %land.lhs.true, %if.then22
  %addsize.1 = phi i32 [ %inc32, %if.then31 ], [ %addsize.0, %land.lhs.true ], [ %addsize.0, %if.then22 ]
  %t34 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i16 = load { float, float }*, { float, float }** %t34, align 8
  %arrayidx35 = getelementptr inbounds { float, float }, { float, float }* %i16, i64 2
  %arrayidx35.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx35, i32 0, i32 0
  %arrayidx35.real = load float, float* %arrayidx35.realp, align 4
  %arrayidx35.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx35, i32 0, i32 1
  %arrayidx35.imag = load float, float* %arrayidx35.imagp, align 4
  %cmp.r36 = fcmp une float %arrayidx35.real, 0.000000e+00
  %cmp.i37 = fcmp une float %arrayidx35.imag, 0.000000e+00
  %or.ri38 = or i1 %cmp.r36, %cmp.i37
  br i1 %or.ri38, label %land.lhs.true39, label %if.end50

land.lhs.true39:                                  ; preds = %if.end33
  %node40 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i17 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node40, align 8
  %idxprom41 = sext i32 %i.2 to i64
  %arrayidx42 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i17, i64 %idxprom41
  %state43 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx42, i32 0, i32 1
  %i18 = load i64, i64* %state43, align 8
  %sh_prom44 = zext i32 %target to i64
  %shl45 = shl i64 1, %sh_prom44
  %and46 = and i64 %i18, %shl45
  %tobool47 = icmp ne i64 %and46, 0
  br i1 %tobool47, label %if.end50, label %if.then48

if.then48:                                        ; preds = %land.lhs.true39
  %inc49 = add nsw i32 %addsize.1, 1
  br label %if.end50

if.end50:                                         ; preds = %if.then48, %land.lhs.true39, %if.end33
  %addsize.2 = phi i32 [ %addsize.1, %land.lhs.true39 ], [ %inc49, %if.then48 ], [ %addsize.1, %if.end33 ]
  br label %if.end51

if.end51:                                         ; preds = %if.end50, %for.body14
  %addsize.3 = phi i32 [ %addsize.2, %if.end50 ], [ %addsize.0, %for.body14 ]
  br label %for.inc52

for.inc52:                                        ; preds = %if.end51
  %inc53 = add nsw i32 %i.2, 1
  br label %for.cond11

for.end54:                                        ; preds = %for.cond11
  %node55 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i19 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node55, align 8
  %i20 = bitcast %struct.quantum_reg_node_struct* %i19 to i8*
  %size56 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i21 = load i32, i32* %size56, align 4
  %add = add nsw i32 %i21, %addsize.0
  %conv = sext i32 %add to i64
  %mul = mul i64 %conv, 16
  %call57 = call i8* @realloc(i8* %i20, i64 %mul) #9
  %i22 = bitcast i8* %call57 to %struct.quantum_reg_node_struct*
  %node58 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i22, %struct.quantum_reg_node_struct** %node58, align 8
  %node59 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i23 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node59, align 8
  %tobool60 = icmp ne %struct.quantum_reg_node_struct* %i23, null
  br i1 %tobool60, label %if.end65, label %if.then61

if.then61:                                        ; preds = %for.end54
  %size62 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i24 = load i32, i32* %size62, align 4
  %add63 = add nsw i32 %i24, %addsize.0
  %call64 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.2, i64 0, i64 0), i32 %add63)
  call void @exit(i32 1) #10
  unreachable

if.end65:                                         ; preds = %for.end54
  %conv66 = sext i32 %addsize.0 to i64
  %mul67 = mul i64 %conv66, 16
  %call68 = call i64 @quantum_memman(i64 %mul67)
  br label %for.cond69

for.cond69:                                       ; preds = %for.inc84, %if.end65
  %i.3 = phi i32 [ 0, %if.end65 ], [ %inc85, %for.inc84 ]
  %cmp70 = icmp slt i32 %i.3, %addsize.0
  br i1 %cmp70, label %for.body72, label %for.end86

for.body72:                                       ; preds = %for.cond69
  %node73 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i25 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node73, align 8
  %size74 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i26 = load i32, i32* %size74, align 4
  %add75 = add nsw i32 %i.3, %i26
  %idxprom76 = sext i32 %add75 to i64
  %arrayidx77 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i25, i64 %idxprom76
  %state78 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx77, i32 0, i32 1
  store i64 0, i64* %state78, align 8
  %node79 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i27 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node79, align 8
  %size80 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i28 = load i32, i32* %size80, align 4
  %add81 = add nsw i32 %i.3, %i28
  %idxprom82 = sext i32 %add81 to i64
  %arrayidx83 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i27, i64 %idxprom82
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx83, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float 0.000000e+00, float* %amplitude.realp, align 8
  store float 0.000000e+00, float* %amplitude.imagp, align 4
  br label %for.inc84

for.inc84:                                        ; preds = %for.body72
  %inc85 = add nsw i32 %i.3, 1
  br label %for.cond69

for.end86:                                        ; preds = %for.cond69
  %size87 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i29 = load i32, i32* %size87, align 4
  %add88 = add nsw i32 %i29, %addsize.0
  %conv89 = sext i32 %add88 to i64
  %call90 = call noalias i8* @calloc(i64 %conv89, i64 1) #9
  %tobool91 = icmp ne i8* %call90, null
  br i1 %tobool91, label %if.end98, label %if.then92

if.then92:                                        ; preds = %for.end86
  %size93 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i30 = load i32, i32* %size93, align 4
  %add94 = add nsw i32 %i30, %addsize.0
  %conv95 = sext i32 %add94 to i64
  %mul96 = mul i64 %conv95, 1
  %call97 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.3, i64 0, i64 0), i64 %mul96)
  call void @exit(i32 1) #10
  unreachable

if.end98:                                         ; preds = %for.end86
  %size99 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i31 = load i32, i32* %size99, align 4
  %conv100 = sext i32 %i31 to i64
  %conv101 = sext i32 %addsize.0 to i64
  %mul102 = mul i64 %conv101, 1
  %add103 = add i64 %conv100, %mul102
  %call104 = call i64 @quantum_memman(i64 %add103)
  %size105 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i32 = load i32, i32* %size105, align 4
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i33 = load i32, i32* %width, align 8
  %sh_prom106 = zext i32 %i33 to i64
  %shl107 = shl i64 1, %sh_prom106
  %conv108 = uitofp i64 %shl107 to double
  %div = fdiv double 1.000000e+00, %conv108
  %div109 = fdiv double %div, 1.000000e+06
  %conv110 = fptrunc double %div109 to float
  br label %for.cond111

for.cond111:                                      ; preds = %for.inc429, %if.end98
  %i.4 = phi i32 [ 0, %if.end98 ], [ %inc430, %for.inc429 ]
  %k.0 = phi i32 [ %i32, %if.end98 ], [ %k.2, %for.inc429 ]
  %size112 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i34 = load i32, i32* %size112, align 4
  %cmp113 = icmp slt i32 %i.4, %i34
  br i1 %cmp113, label %for.body115, label %for.end431

for.body115:                                      ; preds = %for.cond111
  %idxprom116 = sext i32 %i.4 to i64
  %arrayidx117 = getelementptr inbounds i8, i8* %call90, i64 %idxprom116
  %i35 = load i8, i8* %arrayidx117, align 1
  %tobool118 = icmp ne i8 %i35, 0
  br i1 %tobool118, label %if.end428, label %if.then119

if.then119:                                       ; preds = %for.body115
  %node120 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i36 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node120, align 8
  %idxprom121 = sext i32 %i.4 to i64
  %arrayidx122 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i36, i64 %idxprom121
  %state123 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx122, i32 0, i32 1
  %i37 = load i64, i64* %state123, align 8
  %sh_prom124 = zext i32 %target to i64
  %shl125 = shl i64 1, %sh_prom124
  %and126 = and i64 %i37, %shl125
  %conv127 = trunc i64 %and126 to i32
  %tnot.realp128 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.imagp129 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  store float 0.000000e+00, float* %tnot.realp128, align 4
  store float 0.000000e+00, float* %tnot.imagp129, align 4
  %node130 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i38 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node130, align 8
  %idxprom131 = sext i32 %i.4 to i64
  %arrayidx132 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i38, i64 %idxprom131
  %state133 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx132, i32 0, i32 1
  %i39 = load i64, i64* %state133, align 8
  %sh_prom134 = zext i32 %target to i64
  %shl135 = shl i64 1, %sh_prom134
  %xor136 = xor i64 %i39, %shl135
  %call137 = call i32 @quantum_get_state(i64 %xor136, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg)
  %node138 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i40 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node138, align 8
  %idxprom139 = sext i32 %i.4 to i64
  %arrayidx140 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i40, i64 %idxprom139
  %amplitude141 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx140, i32 0, i32 0
  %amplitude141.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude141, i32 0, i32 0
  %amplitude141.real = load float, float* %amplitude141.realp, align 8
  %amplitude141.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude141, i32 0, i32 1
  %amplitude141.imag = load float, float* %amplitude141.imagp, align 4
  %t.realp = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.imagp = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  store float %amplitude141.real, float* %t.realp, align 4
  store float %amplitude141.imag, float* %t.imagp, align 4
  %cmp142 = icmp sge i32 %call137, 0
  br i1 %cmp142, label %if.then144, label %if.end151

if.then144:                                       ; preds = %if.then119
  %node145 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i41 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node145, align 8
  %idxprom146 = sext i32 %call137 to i64
  %arrayidx147 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i41, i64 %idxprom146
  %amplitude148 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx147, i32 0, i32 0
  %amplitude148.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude148, i32 0, i32 0
  %amplitude148.real = load float, float* %amplitude148.realp, align 8
  %amplitude148.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude148, i32 0, i32 1
  %amplitude148.imag = load float, float* %amplitude148.imagp, align 4
  %tnot.realp149 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.imagp150 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  store float %amplitude148.real, float* %tnot.realp149, align 4
  store float %amplitude148.imag, float* %tnot.imagp150, align 4
  br label %if.end151

if.end151:                                        ; preds = %if.then144, %if.then119
  %tobool152 = icmp ne i32 %conv127, 0
  br i1 %tobool152, label %if.then153, label %if.else

if.then153:                                       ; preds = %if.end151
  %t154 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i42 = load { float, float }*, { float, float }** %t154, align 8
  %arrayidx155 = getelementptr inbounds { float, float }, { float, float }* %i42, i64 2
  %arrayidx155.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx155, i32 0, i32 0
  %arrayidx155.real = load float, float* %arrayidx155.realp, align 4
  %arrayidx155.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx155, i32 0, i32 1
  %arrayidx155.imag = load float, float* %arrayidx155.imagp, align 4
  %tnot.realp156 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real = load float, float* %tnot.realp156, align 4
  %tnot.imagp157 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag = load float, float* %tnot.imagp157, align 4
  %mul_ac = fmul float %arrayidx155.real, %tnot.real
  %mul_bd = fmul float %arrayidx155.imag, %tnot.imag
  %mul_ad = fmul float %arrayidx155.real, %tnot.imag
  %mul_bc = fmul float %arrayidx155.imag, %tnot.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then153
  %isnan_cmp158 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp158, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call159 = call <2 x float> @__mulsc3(float %arrayidx155.real, float %arrayidx155.imag, float %tnot.real, float %tnot.imag) #9
  %i43 = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call159, <2 x float>* %i43, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then153
  %real_mul_phi = phi float [ %mul_r, %if.then153 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then153 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce.imag, %complex_mul_libcall ]
  %t160 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i44 = load { float, float }*, { float, float }** %t160, align 8
  %arrayidx161 = getelementptr inbounds { float, float }, { float, float }* %i44, i64 3
  %arrayidx161.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx161, i32 0, i32 0
  %arrayidx161.real = load float, float* %arrayidx161.realp, align 4
  %arrayidx161.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx161, i32 0, i32 1
  %arrayidx161.imag = load float, float* %arrayidx161.imagp, align 4
  %t.realp162 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real = load float, float* %t.realp162, align 4
  %t.imagp163 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag = load float, float* %t.imagp163, align 4
  %mul_ac164 = fmul float %arrayidx161.real, %t.real
  %mul_bd165 = fmul float %arrayidx161.imag, %t.imag
  %mul_ad166 = fmul float %arrayidx161.real, %t.imag
  %mul_bc167 = fmul float %arrayidx161.imag, %t.real
  %mul_r168 = fsub float %mul_ac164, %mul_bd165
  %mul_i169 = fadd float %mul_ad166, %mul_bc167
  %isnan_cmp170 = fcmp uno float %mul_r168, %mul_r168
  br i1 %isnan_cmp170, label %complex_mul_imag_nan171, label %complex_mul_cont176, !prof !2

complex_mul_imag_nan171:                          ; preds = %complex_mul_cont
  %isnan_cmp172 = fcmp uno float %mul_i169, %mul_i169
  br i1 %isnan_cmp172, label %complex_mul_libcall173, label %complex_mul_cont176, !prof !2

complex_mul_libcall173:                           ; preds = %complex_mul_imag_nan171
  %call174 = call <2 x float> @__mulsc3(float %arrayidx161.real, float %arrayidx161.imag, float %t.real, float %t.imag) #9
  %i45 = bitcast { float, float }* %coerce175 to <2 x float>*
  store <2 x float> %call174, <2 x float>* %i45, align 4
  %coerce175.realp = getelementptr inbounds { float, float }, { float, float }* %coerce175, i32 0, i32 0
  %coerce175.real = load float, float* %coerce175.realp, align 4
  %coerce175.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce175, i32 0, i32 1
  %coerce175.imag = load float, float* %coerce175.imagp, align 4
  br label %complex_mul_cont176

complex_mul_cont176:                              ; preds = %complex_mul_libcall173, %complex_mul_imag_nan171, %complex_mul_cont
  %real_mul_phi177 = phi float [ %mul_r168, %complex_mul_cont ], [ %mul_r168, %complex_mul_imag_nan171 ], [ %coerce175.real, %complex_mul_libcall173 ]
  %imag_mul_phi178 = phi float [ %mul_i169, %complex_mul_cont ], [ %mul_i169, %complex_mul_imag_nan171 ], [ %coerce175.imag, %complex_mul_libcall173 ]
  %add.r = fadd float %real_mul_phi, %real_mul_phi177
  %add.i = fadd float %imag_mul_phi, %imag_mul_phi178
  %node179 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i46 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node179, align 8
  %idxprom180 = sext i32 %i.4 to i64
  %arrayidx181 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i46, i64 %idxprom180
  %amplitude182 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx181, i32 0, i32 0
  %amplitude182.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude182, i32 0, i32 0
  %amplitude182.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude182, i32 0, i32 1
  store float %add.r, float* %amplitude182.realp, align 8
  store float %add.i, float* %amplitude182.imagp, align 4
  br label %if.end231

if.else:                                          ; preds = %if.end151
  %t183 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i47 = load { float, float }*, { float, float }** %t183, align 8
  %arrayidx184 = getelementptr inbounds { float, float }, { float, float }* %i47, i64 0
  %arrayidx184.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx184, i32 0, i32 0
  %arrayidx184.real = load float, float* %arrayidx184.realp, align 4
  %arrayidx184.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx184, i32 0, i32 1
  %arrayidx184.imag = load float, float* %arrayidx184.imagp, align 4
  %t.realp185 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real186 = load float, float* %t.realp185, align 4
  %t.imagp187 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag188 = load float, float* %t.imagp187, align 4
  %mul_ac189 = fmul float %arrayidx184.real, %t.real186
  %mul_bd190 = fmul float %arrayidx184.imag, %t.imag188
  %mul_ad191 = fmul float %arrayidx184.real, %t.imag188
  %mul_bc192 = fmul float %arrayidx184.imag, %t.real186
  %mul_r193 = fsub float %mul_ac189, %mul_bd190
  %mul_i194 = fadd float %mul_ad191, %mul_bc192
  %isnan_cmp195 = fcmp uno float %mul_r193, %mul_r193
  br i1 %isnan_cmp195, label %complex_mul_imag_nan196, label %complex_mul_cont201, !prof !2

complex_mul_imag_nan196:                          ; preds = %if.else
  %isnan_cmp197 = fcmp uno float %mul_i194, %mul_i194
  br i1 %isnan_cmp197, label %complex_mul_libcall198, label %complex_mul_cont201, !prof !2

complex_mul_libcall198:                           ; preds = %complex_mul_imag_nan196
  %call199 = call <2 x float> @__mulsc3(float %arrayidx184.real, float %arrayidx184.imag, float %t.real186, float %t.imag188) #9
  %i48 = bitcast { float, float }* %coerce200 to <2 x float>*
  store <2 x float> %call199, <2 x float>* %i48, align 4
  %coerce200.realp = getelementptr inbounds { float, float }, { float, float }* %coerce200, i32 0, i32 0
  %coerce200.real = load float, float* %coerce200.realp, align 4
  %coerce200.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce200, i32 0, i32 1
  %coerce200.imag = load float, float* %coerce200.imagp, align 4
  br label %complex_mul_cont201

complex_mul_cont201:                              ; preds = %complex_mul_libcall198, %complex_mul_imag_nan196, %if.else
  %real_mul_phi202 = phi float [ %mul_r193, %if.else ], [ %mul_r193, %complex_mul_imag_nan196 ], [ %coerce200.real, %complex_mul_libcall198 ]
  %imag_mul_phi203 = phi float [ %mul_i194, %if.else ], [ %mul_i194, %complex_mul_imag_nan196 ], [ %coerce200.imag, %complex_mul_libcall198 ]
  %t204 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i49 = load { float, float }*, { float, float }** %t204, align 8
  %arrayidx205 = getelementptr inbounds { float, float }, { float, float }* %i49, i64 1
  %arrayidx205.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx205, i32 0, i32 0
  %arrayidx205.real = load float, float* %arrayidx205.realp, align 4
  %arrayidx205.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx205, i32 0, i32 1
  %arrayidx205.imag = load float, float* %arrayidx205.imagp, align 4
  %tnot.realp206 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real207 = load float, float* %tnot.realp206, align 4
  %tnot.imagp208 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag209 = load float, float* %tnot.imagp208, align 4
  %mul_ac210 = fmul float %arrayidx205.real, %tnot.real207
  %mul_bd211 = fmul float %arrayidx205.imag, %tnot.imag209
  %mul_ad212 = fmul float %arrayidx205.real, %tnot.imag209
  %mul_bc213 = fmul float %arrayidx205.imag, %tnot.real207
  %mul_r214 = fsub float %mul_ac210, %mul_bd211
  %mul_i215 = fadd float %mul_ad212, %mul_bc213
  %isnan_cmp216 = fcmp uno float %mul_r214, %mul_r214
  br i1 %isnan_cmp216, label %complex_mul_imag_nan217, label %complex_mul_cont222, !prof !2

complex_mul_imag_nan217:                          ; preds = %complex_mul_cont201
  %isnan_cmp218 = fcmp uno float %mul_i215, %mul_i215
  br i1 %isnan_cmp218, label %complex_mul_libcall219, label %complex_mul_cont222, !prof !2

complex_mul_libcall219:                           ; preds = %complex_mul_imag_nan217
  %call220 = call <2 x float> @__mulsc3(float %arrayidx205.real, float %arrayidx205.imag, float %tnot.real207, float %tnot.imag209) #9
  %i50 = bitcast { float, float }* %coerce221 to <2 x float>*
  store <2 x float> %call220, <2 x float>* %i50, align 4
  %coerce221.realp = getelementptr inbounds { float, float }, { float, float }* %coerce221, i32 0, i32 0
  %coerce221.real = load float, float* %coerce221.realp, align 4
  %coerce221.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce221, i32 0, i32 1
  %coerce221.imag = load float, float* %coerce221.imagp, align 4
  br label %complex_mul_cont222

complex_mul_cont222:                              ; preds = %complex_mul_libcall219, %complex_mul_imag_nan217, %complex_mul_cont201
  %real_mul_phi223 = phi float [ %mul_r214, %complex_mul_cont201 ], [ %mul_r214, %complex_mul_imag_nan217 ], [ %coerce221.real, %complex_mul_libcall219 ]
  %imag_mul_phi224 = phi float [ %mul_i215, %complex_mul_cont201 ], [ %mul_i215, %complex_mul_imag_nan217 ], [ %coerce221.imag, %complex_mul_libcall219 ]
  %add.r225 = fadd float %real_mul_phi202, %real_mul_phi223
  %add.i226 = fadd float %imag_mul_phi203, %imag_mul_phi224
  %node227 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i51 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node227, align 8
  %idxprom228 = sext i32 %i.4 to i64
  %arrayidx229 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i51, i64 %idxprom228
  %amplitude230 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx229, i32 0, i32 0
  %amplitude230.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude230, i32 0, i32 0
  %amplitude230.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude230, i32 0, i32 1
  store float %add.r225, float* %amplitude230.realp, align 8
  store float %add.i226, float* %amplitude230.imagp, align 4
  br label %if.end231

if.end231:                                        ; preds = %complex_mul_cont222, %complex_mul_cont176
  %cmp232 = icmp sge i32 %call137, 0
  br i1 %cmp232, label %if.then234, label %if.else335

if.then234:                                       ; preds = %if.end231
  %tobool235 = icmp ne i32 %conv127, 0
  br i1 %tobool235, label %if.then236, label %if.else285

if.then236:                                       ; preds = %if.then234
  %t237 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i52 = load { float, float }*, { float, float }** %t237, align 8
  %arrayidx238 = getelementptr inbounds { float, float }, { float, float }* %i52, i64 0
  %arrayidx238.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx238, i32 0, i32 0
  %arrayidx238.real = load float, float* %arrayidx238.realp, align 4
  %arrayidx238.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx238, i32 0, i32 1
  %arrayidx238.imag = load float, float* %arrayidx238.imagp, align 4
  %tnot.realp239 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real240 = load float, float* %tnot.realp239, align 4
  %tnot.imagp241 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag242 = load float, float* %tnot.imagp241, align 4
  %mul_ac243 = fmul float %arrayidx238.real, %tnot.real240
  %mul_bd244 = fmul float %arrayidx238.imag, %tnot.imag242
  %mul_ad245 = fmul float %arrayidx238.real, %tnot.imag242
  %mul_bc246 = fmul float %arrayidx238.imag, %tnot.real240
  %mul_r247 = fsub float %mul_ac243, %mul_bd244
  %mul_i248 = fadd float %mul_ad245, %mul_bc246
  %isnan_cmp249 = fcmp uno float %mul_r247, %mul_r247
  br i1 %isnan_cmp249, label %complex_mul_imag_nan250, label %complex_mul_cont255, !prof !2

complex_mul_imag_nan250:                          ; preds = %if.then236
  %isnan_cmp251 = fcmp uno float %mul_i248, %mul_i248
  br i1 %isnan_cmp251, label %complex_mul_libcall252, label %complex_mul_cont255, !prof !2

complex_mul_libcall252:                           ; preds = %complex_mul_imag_nan250
  %call253 = call <2 x float> @__mulsc3(float %arrayidx238.real, float %arrayidx238.imag, float %tnot.real240, float %tnot.imag242) #9
  %i53 = bitcast { float, float }* %coerce254 to <2 x float>*
  store <2 x float> %call253, <2 x float>* %i53, align 4
  %coerce254.realp = getelementptr inbounds { float, float }, { float, float }* %coerce254, i32 0, i32 0
  %coerce254.real = load float, float* %coerce254.realp, align 4
  %coerce254.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce254, i32 0, i32 1
  %coerce254.imag = load float, float* %coerce254.imagp, align 4
  br label %complex_mul_cont255

complex_mul_cont255:                              ; preds = %complex_mul_libcall252, %complex_mul_imag_nan250, %if.then236
  %real_mul_phi256 = phi float [ %mul_r247, %if.then236 ], [ %mul_r247, %complex_mul_imag_nan250 ], [ %coerce254.real, %complex_mul_libcall252 ]
  %imag_mul_phi257 = phi float [ %mul_i248, %if.then236 ], [ %mul_i248, %complex_mul_imag_nan250 ], [ %coerce254.imag, %complex_mul_libcall252 ]
  %t258 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i54 = load { float, float }*, { float, float }** %t258, align 8
  %arrayidx259 = getelementptr inbounds { float, float }, { float, float }* %i54, i64 1
  %arrayidx259.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx259, i32 0, i32 0
  %arrayidx259.real = load float, float* %arrayidx259.realp, align 4
  %arrayidx259.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx259, i32 0, i32 1
  %arrayidx259.imag = load float, float* %arrayidx259.imagp, align 4
  %t.realp260 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real261 = load float, float* %t.realp260, align 4
  %t.imagp262 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag263 = load float, float* %t.imagp262, align 4
  %mul_ac264 = fmul float %arrayidx259.real, %t.real261
  %mul_bd265 = fmul float %arrayidx259.imag, %t.imag263
  %mul_ad266 = fmul float %arrayidx259.real, %t.imag263
  %mul_bc267 = fmul float %arrayidx259.imag, %t.real261
  %mul_r268 = fsub float %mul_ac264, %mul_bd265
  %mul_i269 = fadd float %mul_ad266, %mul_bc267
  %isnan_cmp270 = fcmp uno float %mul_r268, %mul_r268
  br i1 %isnan_cmp270, label %complex_mul_imag_nan271, label %complex_mul_cont276, !prof !2

complex_mul_imag_nan271:                          ; preds = %complex_mul_cont255
  %isnan_cmp272 = fcmp uno float %mul_i269, %mul_i269
  br i1 %isnan_cmp272, label %complex_mul_libcall273, label %complex_mul_cont276, !prof !2

complex_mul_libcall273:                           ; preds = %complex_mul_imag_nan271
  %call274 = call <2 x float> @__mulsc3(float %arrayidx259.real, float %arrayidx259.imag, float %t.real261, float %t.imag263) #9
  %i55 = bitcast { float, float }* %coerce275 to <2 x float>*
  store <2 x float> %call274, <2 x float>* %i55, align 4
  %coerce275.realp = getelementptr inbounds { float, float }, { float, float }* %coerce275, i32 0, i32 0
  %coerce275.real = load float, float* %coerce275.realp, align 4
  %coerce275.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce275, i32 0, i32 1
  %coerce275.imag = load float, float* %coerce275.imagp, align 4
  br label %complex_mul_cont276

complex_mul_cont276:                              ; preds = %complex_mul_libcall273, %complex_mul_imag_nan271, %complex_mul_cont255
  %real_mul_phi277 = phi float [ %mul_r268, %complex_mul_cont255 ], [ %mul_r268, %complex_mul_imag_nan271 ], [ %coerce275.real, %complex_mul_libcall273 ]
  %imag_mul_phi278 = phi float [ %mul_i269, %complex_mul_cont255 ], [ %mul_i269, %complex_mul_imag_nan271 ], [ %coerce275.imag, %complex_mul_libcall273 ]
  %add.r279 = fadd float %real_mul_phi256, %real_mul_phi277
  %add.i280 = fadd float %imag_mul_phi257, %imag_mul_phi278
  %node281 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i56 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node281, align 8
  %idxprom282 = sext i32 %call137 to i64
  %arrayidx283 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i56, i64 %idxprom282
  %amplitude284 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx283, i32 0, i32 0
  %amplitude284.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude284, i32 0, i32 0
  %amplitude284.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude284, i32 0, i32 1
  store float %add.r279, float* %amplitude284.realp, align 8
  store float %add.i280, float* %amplitude284.imagp, align 4
  br label %if.end334

if.else285:                                       ; preds = %if.then234
  %t286 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i57 = load { float, float }*, { float, float }** %t286, align 8
  %arrayidx287 = getelementptr inbounds { float, float }, { float, float }* %i57, i64 2
  %arrayidx287.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx287, i32 0, i32 0
  %arrayidx287.real = load float, float* %arrayidx287.realp, align 4
  %arrayidx287.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx287, i32 0, i32 1
  %arrayidx287.imag = load float, float* %arrayidx287.imagp, align 4
  %t.realp288 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real289 = load float, float* %t.realp288, align 4
  %t.imagp290 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag291 = load float, float* %t.imagp290, align 4
  %mul_ac292 = fmul float %arrayidx287.real, %t.real289
  %mul_bd293 = fmul float %arrayidx287.imag, %t.imag291
  %mul_ad294 = fmul float %arrayidx287.real, %t.imag291
  %mul_bc295 = fmul float %arrayidx287.imag, %t.real289
  %mul_r296 = fsub float %mul_ac292, %mul_bd293
  %mul_i297 = fadd float %mul_ad294, %mul_bc295
  %isnan_cmp298 = fcmp uno float %mul_r296, %mul_r296
  br i1 %isnan_cmp298, label %complex_mul_imag_nan299, label %complex_mul_cont304, !prof !2

complex_mul_imag_nan299:                          ; preds = %if.else285
  %isnan_cmp300 = fcmp uno float %mul_i297, %mul_i297
  br i1 %isnan_cmp300, label %complex_mul_libcall301, label %complex_mul_cont304, !prof !2

complex_mul_libcall301:                           ; preds = %complex_mul_imag_nan299
  %call302 = call <2 x float> @__mulsc3(float %arrayidx287.real, float %arrayidx287.imag, float %t.real289, float %t.imag291) #9
  %i58 = bitcast { float, float }* %coerce303 to <2 x float>*
  store <2 x float> %call302, <2 x float>* %i58, align 4
  %coerce303.realp = getelementptr inbounds { float, float }, { float, float }* %coerce303, i32 0, i32 0
  %coerce303.real = load float, float* %coerce303.realp, align 4
  %coerce303.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce303, i32 0, i32 1
  %coerce303.imag = load float, float* %coerce303.imagp, align 4
  br label %complex_mul_cont304

complex_mul_cont304:                              ; preds = %complex_mul_libcall301, %complex_mul_imag_nan299, %if.else285
  %real_mul_phi305 = phi float [ %mul_r296, %if.else285 ], [ %mul_r296, %complex_mul_imag_nan299 ], [ %coerce303.real, %complex_mul_libcall301 ]
  %imag_mul_phi306 = phi float [ %mul_i297, %if.else285 ], [ %mul_i297, %complex_mul_imag_nan299 ], [ %coerce303.imag, %complex_mul_libcall301 ]
  %t307 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i59 = load { float, float }*, { float, float }** %t307, align 8
  %arrayidx308 = getelementptr inbounds { float, float }, { float, float }* %i59, i64 3
  %arrayidx308.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx308, i32 0, i32 0
  %arrayidx308.real = load float, float* %arrayidx308.realp, align 4
  %arrayidx308.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx308, i32 0, i32 1
  %arrayidx308.imag = load float, float* %arrayidx308.imagp, align 4
  %tnot.realp309 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 0
  %tnot.real310 = load float, float* %tnot.realp309, align 4
  %tnot.imagp311 = getelementptr inbounds { float, float }, { float, float }* %tnot, i32 0, i32 1
  %tnot.imag312 = load float, float* %tnot.imagp311, align 4
  %mul_ac313 = fmul float %arrayidx308.real, %tnot.real310
  %mul_bd314 = fmul float %arrayidx308.imag, %tnot.imag312
  %mul_ad315 = fmul float %arrayidx308.real, %tnot.imag312
  %mul_bc316 = fmul float %arrayidx308.imag, %tnot.real310
  %mul_r317 = fsub float %mul_ac313, %mul_bd314
  %mul_i318 = fadd float %mul_ad315, %mul_bc316
  %isnan_cmp319 = fcmp uno float %mul_r317, %mul_r317
  br i1 %isnan_cmp319, label %complex_mul_imag_nan320, label %complex_mul_cont325, !prof !2

complex_mul_imag_nan320:                          ; preds = %complex_mul_cont304
  %isnan_cmp321 = fcmp uno float %mul_i318, %mul_i318
  br i1 %isnan_cmp321, label %complex_mul_libcall322, label %complex_mul_cont325, !prof !2

complex_mul_libcall322:                           ; preds = %complex_mul_imag_nan320
  %call323 = call <2 x float> @__mulsc3(float %arrayidx308.real, float %arrayidx308.imag, float %tnot.real310, float %tnot.imag312) #9
  %i60 = bitcast { float, float }* %coerce324 to <2 x float>*
  store <2 x float> %call323, <2 x float>* %i60, align 4
  %coerce324.realp = getelementptr inbounds { float, float }, { float, float }* %coerce324, i32 0, i32 0
  %coerce324.real = load float, float* %coerce324.realp, align 4
  %coerce324.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce324, i32 0, i32 1
  %coerce324.imag = load float, float* %coerce324.imagp, align 4
  br label %complex_mul_cont325

complex_mul_cont325:                              ; preds = %complex_mul_libcall322, %complex_mul_imag_nan320, %complex_mul_cont304
  %real_mul_phi326 = phi float [ %mul_r317, %complex_mul_cont304 ], [ %mul_r317, %complex_mul_imag_nan320 ], [ %coerce324.real, %complex_mul_libcall322 ]
  %imag_mul_phi327 = phi float [ %mul_i318, %complex_mul_cont304 ], [ %mul_i318, %complex_mul_imag_nan320 ], [ %coerce324.imag, %complex_mul_libcall322 ]
  %add.r328 = fadd float %real_mul_phi305, %real_mul_phi326
  %add.i329 = fadd float %imag_mul_phi306, %imag_mul_phi327
  %node330 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i61 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node330, align 8
  %idxprom331 = sext i32 %call137 to i64
  %arrayidx332 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i61, i64 %idxprom331
  %amplitude333 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx332, i32 0, i32 0
  %amplitude333.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude333, i32 0, i32 0
  %amplitude333.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude333, i32 0, i32 1
  store float %add.r328, float* %amplitude333.realp, align 8
  store float %add.i329, float* %amplitude333.imagp, align 4
  br label %if.end334

if.end334:                                        ; preds = %complex_mul_cont325, %complex_mul_cont276
  br label %if.end421

if.else335:                                       ; preds = %if.end231
  %t336 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i62 = load { float, float }*, { float, float }** %t336, align 8
  %arrayidx337 = getelementptr inbounds { float, float }, { float, float }* %i62, i64 1
  %arrayidx337.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx337, i32 0, i32 0
  %arrayidx337.real = load float, float* %arrayidx337.realp, align 4
  %arrayidx337.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx337, i32 0, i32 1
  %arrayidx337.imag = load float, float* %arrayidx337.imagp, align 4
  %cmp.r338 = fcmp oeq float %arrayidx337.real, 0.000000e+00
  %cmp.i339 = fcmp oeq float %arrayidx337.imag, 0.000000e+00
  %and.ri = and i1 %cmp.r338, %cmp.i339
  br i1 %and.ri, label %land.lhs.true341, label %if.end344

land.lhs.true341:                                 ; preds = %if.else335
  %tobool342 = icmp ne i32 %conv127, 0
  br i1 %tobool342, label %if.then343, label %if.end344

if.then343:                                       ; preds = %land.lhs.true341
  br label %for.end431

if.end344:                                        ; preds = %land.lhs.true341, %if.else335
  %t345 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i63 = load { float, float }*, { float, float }** %t345, align 8
  %arrayidx346 = getelementptr inbounds { float, float }, { float, float }* %i63, i64 2
  %arrayidx346.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx346, i32 0, i32 0
  %arrayidx346.real = load float, float* %arrayidx346.realp, align 4
  %arrayidx346.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx346, i32 0, i32 1
  %arrayidx346.imag = load float, float* %arrayidx346.imagp, align 4
  %cmp.r347 = fcmp oeq float %arrayidx346.real, 0.000000e+00
  %cmp.i348 = fcmp oeq float %arrayidx346.imag, 0.000000e+00
  %and.ri349 = and i1 %cmp.r347, %cmp.i348
  br i1 %and.ri349, label %land.lhs.true351, label %if.end354

land.lhs.true351:                                 ; preds = %if.end344
  %tobool352 = icmp ne i32 %conv127, 0
  br i1 %tobool352, label %if.end354, label %if.then353

if.then353:                                       ; preds = %land.lhs.true351
  br label %for.end431

if.end354:                                        ; preds = %land.lhs.true351, %if.end344
  %node355 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i64 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node355, align 8
  %idxprom356 = sext i32 %i.4 to i64
  %arrayidx357 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i64, i64 %idxprom356
  %state358 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx357, i32 0, i32 1
  %i65 = load i64, i64* %state358, align 8
  %sh_prom359 = zext i32 %target to i64
  %shl360 = shl i64 1, %sh_prom359
  %xor361 = xor i64 %i65, %shl360
  %node362 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i66 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node362, align 8
  %idxprom363 = sext i32 %k.0 to i64
  %arrayidx364 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i66, i64 %idxprom363
  %state365 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx364, i32 0, i32 1
  store i64 %xor361, i64* %state365, align 8
  %tobool366 = icmp ne i32 %conv127, 0
  br i1 %tobool366, label %if.then367, label %if.else393

if.then367:                                       ; preds = %if.end354
  %t368 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i67 = load { float, float }*, { float, float }** %t368, align 8
  %arrayidx369 = getelementptr inbounds { float, float }, { float, float }* %i67, i64 1
  %arrayidx369.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx369, i32 0, i32 0
  %arrayidx369.real = load float, float* %arrayidx369.realp, align 4
  %arrayidx369.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx369, i32 0, i32 1
  %arrayidx369.imag = load float, float* %arrayidx369.imagp, align 4
  %t.realp370 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real371 = load float, float* %t.realp370, align 4
  %t.imagp372 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag373 = load float, float* %t.imagp372, align 4
  %mul_ac374 = fmul float %arrayidx369.real, %t.real371
  %mul_bd375 = fmul float %arrayidx369.imag, %t.imag373
  %mul_ad376 = fmul float %arrayidx369.real, %t.imag373
  %mul_bc377 = fmul float %arrayidx369.imag, %t.real371
  %mul_r378 = fsub float %mul_ac374, %mul_bd375
  %mul_i379 = fadd float %mul_ad376, %mul_bc377
  %isnan_cmp380 = fcmp uno float %mul_r378, %mul_r378
  br i1 %isnan_cmp380, label %complex_mul_imag_nan381, label %complex_mul_cont386, !prof !2

complex_mul_imag_nan381:                          ; preds = %if.then367
  %isnan_cmp382 = fcmp uno float %mul_i379, %mul_i379
  br i1 %isnan_cmp382, label %complex_mul_libcall383, label %complex_mul_cont386, !prof !2

complex_mul_libcall383:                           ; preds = %complex_mul_imag_nan381
  %call384 = call <2 x float> @__mulsc3(float %arrayidx369.real, float %arrayidx369.imag, float %t.real371, float %t.imag373) #9
  %i68 = bitcast { float, float }* %coerce385 to <2 x float>*
  store <2 x float> %call384, <2 x float>* %i68, align 4
  %coerce385.realp = getelementptr inbounds { float, float }, { float, float }* %coerce385, i32 0, i32 0
  %coerce385.real = load float, float* %coerce385.realp, align 4
  %coerce385.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce385, i32 0, i32 1
  %coerce385.imag = load float, float* %coerce385.imagp, align 4
  br label %complex_mul_cont386

complex_mul_cont386:                              ; preds = %complex_mul_libcall383, %complex_mul_imag_nan381, %if.then367
  %real_mul_phi387 = phi float [ %mul_r378, %if.then367 ], [ %mul_r378, %complex_mul_imag_nan381 ], [ %coerce385.real, %complex_mul_libcall383 ]
  %imag_mul_phi388 = phi float [ %mul_i379, %if.then367 ], [ %mul_i379, %complex_mul_imag_nan381 ], [ %coerce385.imag, %complex_mul_libcall383 ]
  %node389 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i69 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node389, align 8
  %idxprom390 = sext i32 %k.0 to i64
  %arrayidx391 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i69, i64 %idxprom390
  %amplitude392 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx391, i32 0, i32 0
  %amplitude392.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude392, i32 0, i32 0
  %amplitude392.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude392, i32 0, i32 1
  store float %real_mul_phi387, float* %amplitude392.realp, align 8
  store float %imag_mul_phi388, float* %amplitude392.imagp, align 4
  br label %if.end419

if.else393:                                       ; preds = %if.end354
  %t394 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i70 = load { float, float }*, { float, float }** %t394, align 8
  %arrayidx395 = getelementptr inbounds { float, float }, { float, float }* %i70, i64 2
  %arrayidx395.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx395, i32 0, i32 0
  %arrayidx395.real = load float, float* %arrayidx395.realp, align 4
  %arrayidx395.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx395, i32 0, i32 1
  %arrayidx395.imag = load float, float* %arrayidx395.imagp, align 4
  %t.realp396 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 0
  %t.real397 = load float, float* %t.realp396, align 4
  %t.imagp398 = getelementptr inbounds { float, float }, { float, float }* %t, i32 0, i32 1
  %t.imag399 = load float, float* %t.imagp398, align 4
  %mul_ac400 = fmul float %arrayidx395.real, %t.real397
  %mul_bd401 = fmul float %arrayidx395.imag, %t.imag399
  %mul_ad402 = fmul float %arrayidx395.real, %t.imag399
  %mul_bc403 = fmul float %arrayidx395.imag, %t.real397
  %mul_r404 = fsub float %mul_ac400, %mul_bd401
  %mul_i405 = fadd float %mul_ad402, %mul_bc403
  %isnan_cmp406 = fcmp uno float %mul_r404, %mul_r404
  br i1 %isnan_cmp406, label %complex_mul_imag_nan407, label %complex_mul_cont412, !prof !2

complex_mul_imag_nan407:                          ; preds = %if.else393
  %isnan_cmp408 = fcmp uno float %mul_i405, %mul_i405
  br i1 %isnan_cmp408, label %complex_mul_libcall409, label %complex_mul_cont412, !prof !2

complex_mul_libcall409:                           ; preds = %complex_mul_imag_nan407
  %call410 = call <2 x float> @__mulsc3(float %arrayidx395.real, float %arrayidx395.imag, float %t.real397, float %t.imag399) #9
  %i71 = bitcast { float, float }* %coerce411 to <2 x float>*
  store <2 x float> %call410, <2 x float>* %i71, align 4
  %coerce411.realp = getelementptr inbounds { float, float }, { float, float }* %coerce411, i32 0, i32 0
  %coerce411.real = load float, float* %coerce411.realp, align 4
  %coerce411.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce411, i32 0, i32 1
  %coerce411.imag = load float, float* %coerce411.imagp, align 4
  br label %complex_mul_cont412

complex_mul_cont412:                              ; preds = %complex_mul_libcall409, %complex_mul_imag_nan407, %if.else393
  %real_mul_phi413 = phi float [ %mul_r404, %if.else393 ], [ %mul_r404, %complex_mul_imag_nan407 ], [ %coerce411.real, %complex_mul_libcall409 ]
  %imag_mul_phi414 = phi float [ %mul_i405, %if.else393 ], [ %mul_i405, %complex_mul_imag_nan407 ], [ %coerce411.imag, %complex_mul_libcall409 ]
  %node415 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i72 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node415, align 8
  %idxprom416 = sext i32 %k.0 to i64
  %arrayidx417 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i72, i64 %idxprom416
  %amplitude418 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx417, i32 0, i32 0
  %amplitude418.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude418, i32 0, i32 0
  %amplitude418.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude418, i32 0, i32 1
  store float %real_mul_phi413, float* %amplitude418.realp, align 8
  store float %imag_mul_phi414, float* %amplitude418.imagp, align 4
  br label %if.end419

if.end419:                                        ; preds = %complex_mul_cont412, %complex_mul_cont386
  %inc420 = add nsw i32 %k.0, 1
  br label %if.end421

if.end421:                                        ; preds = %if.end419, %if.end334
  %k.1 = phi i32 [ %k.0, %if.end334 ], [ %inc420, %if.end419 ]
  %cmp422 = icmp sge i32 %call137, 0
  br i1 %cmp422, label %if.then424, label %if.end427

if.then424:                                       ; preds = %if.end421
  %idxprom425 = sext i32 %call137 to i64
  %arrayidx426 = getelementptr inbounds i8, i8* %call90, i64 %idxprom425
  store i8 1, i8* %arrayidx426, align 1
  br label %if.end427

if.end427:                                        ; preds = %if.then424, %if.end421
  br label %if.end428

if.end428:                                        ; preds = %if.end427, %for.body115
  %k.2 = phi i32 [ %k.0, %for.body115 ], [ %k.1, %if.end427 ]
  br label %for.inc429

for.inc429:                                       ; preds = %if.end428
  %inc430 = add nsw i32 %i.4, 1
  br label %for.cond111

for.end431:                                       ; preds = %if.then353, %if.then343, %for.cond111
  %size432 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i73 = load i32, i32* %size432, align 4
  %add433 = add nsw i32 %i73, %addsize.0
  store i32 %add433, i32* %size432, align 4
  call void @free(i8* %call90) #9
  %size434 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i74 = load i32, i32* %size434, align 4
  %sub = sub nsw i32 0, %i74
  %conv435 = sext i32 %sub to i64
  %mul436 = mul i64 %conv435, 1
  %call437 = call i64 @quantum_memman(i64 %mul436)
  br label %for.cond438

for.cond438:                                      ; preds = %for.inc477, %for.end431
  %j.0 = phi i32 [ 0, %for.end431 ], [ %j.1, %for.inc477 ]
  %i.5 = phi i32 [ 0, %for.end431 ], [ %inc478, %for.inc477 ]
  %decsize.0 = phi i32 [ 0, %for.end431 ], [ %decsize.1, %for.inc477 ]
  %size439 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i75 = load i32, i32* %size439, align 4
  %cmp440 = icmp slt i32 %i.5, %i75
  br i1 %cmp440, label %for.body442, label %for.end479

for.body442:                                      ; preds = %for.cond438
  %node443 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i76 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node443, align 8
  %idxprom444 = sext i32 %i.5 to i64
  %arrayidx445 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i76, i64 %idxprom444
  %amplitude446 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx445, i32 0, i32 0
  %amplitude446.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude446, i32 0, i32 0
  %amplitude446.real = load float, float* %amplitude446.realp, align 8
  %amplitude446.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude446, i32 0, i32 1
  %amplitude446.imag = load float, float* %amplitude446.imagp, align 4
  %coerce447.realp = getelementptr inbounds { float, float }, { float, float }* %coerce447, i32 0, i32 0
  %coerce447.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce447, i32 0, i32 1
  store float %amplitude446.real, float* %coerce447.realp, align 4
  store float %amplitude446.imag, float* %coerce447.imagp, align 4
  %i77 = bitcast { float, float }* %coerce447 to <2 x float>*
  %i78 = load <2 x float>, <2 x float>* %i77, align 4
  %call448 = call float @quantum_prob_inline.5(<2 x float> %i78)
  %cmp449 = fcmp olt float %call448, %conv110
  br i1 %cmp449, label %if.then451, label %if.else454

if.then451:                                       ; preds = %for.body442
  %inc452 = add nsw i32 %j.0, 1
  %inc453 = add nsw i32 %decsize.0, 1
  br label %if.end476

if.else454:                                       ; preds = %for.body442
  %tobool455 = icmp ne i32 %j.0, 0
  br i1 %tobool455, label %if.then456, label %if.end475

if.then456:                                       ; preds = %if.else454
  %node457 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i79 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node457, align 8
  %idxprom458 = sext i32 %i.5 to i64
  %arrayidx459 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i79, i64 %idxprom458
  %state460 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx459, i32 0, i32 1
  %i80 = load i64, i64* %state460, align 8
  %node461 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i81 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node461, align 8
  %sub462 = sub nsw i32 %i.5, %j.0
  %idxprom463 = sext i32 %sub462 to i64
  %arrayidx464 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i81, i64 %idxprom463
  %state465 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx464, i32 0, i32 1
  store i64 %i80, i64* %state465, align 8
  %node466 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i82 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node466, align 8
  %idxprom467 = sext i32 %i.5 to i64
  %arrayidx468 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i82, i64 %idxprom467
  %amplitude469 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx468, i32 0, i32 0
  %amplitude469.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude469, i32 0, i32 0
  %amplitude469.real = load float, float* %amplitude469.realp, align 8
  %amplitude469.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude469, i32 0, i32 1
  %amplitude469.imag = load float, float* %amplitude469.imagp, align 4
  %node470 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i83 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node470, align 8
  %sub471 = sub nsw i32 %i.5, %j.0
  %idxprom472 = sext i32 %sub471 to i64
  %arrayidx473 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i83, i64 %idxprom472
  %amplitude474 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx473, i32 0, i32 0
  %amplitude474.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude474, i32 0, i32 0
  %amplitude474.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude474, i32 0, i32 1
  store float %amplitude469.real, float* %amplitude474.realp, align 8
  store float %amplitude469.imag, float* %amplitude474.imagp, align 4
  br label %if.end475

if.end475:                                        ; preds = %if.then456, %if.else454
  br label %if.end476

if.end476:                                        ; preds = %if.end475, %if.then451
  %j.1 = phi i32 [ %inc452, %if.then451 ], [ %j.0, %if.end475 ]
  %decsize.1 = phi i32 [ %inc453, %if.then451 ], [ %decsize.0, %if.end475 ]
  br label %for.inc477

for.inc477:                                       ; preds = %if.end476
  %inc478 = add nsw i32 %i.5, 1
  br label %for.cond438

for.end479:                                       ; preds = %for.cond438
  %tobool480 = icmp ne i32 %decsize.0, 0
  br i1 %tobool480, label %if.then481, label %if.end501

if.then481:                                       ; preds = %for.end479
  %size482 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i84 = load i32, i32* %size482, align 4
  %sub483 = sub nsw i32 %i84, %decsize.0
  store i32 %sub483, i32* %size482, align 4
  %node484 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i85 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node484, align 8
  %i86 = bitcast %struct.quantum_reg_node_struct* %i85 to i8*
  %size485 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i87 = load i32, i32* %size485, align 4
  %conv486 = sext i32 %i87 to i64
  %mul487 = mul i64 %conv486, 16
  %call488 = call i8* @realloc(i8* %i86, i64 %mul487) #9
  %i88 = bitcast i8* %call488 to %struct.quantum_reg_node_struct*
  %node489 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i88, %struct.quantum_reg_node_struct** %node489, align 8
  %node490 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i89 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node490, align 8
  %tobool491 = icmp ne %struct.quantum_reg_node_struct* %i89, null
  br i1 %tobool491, label %if.end496, label %if.then492

if.then492:                                       ; preds = %if.then481
  %size493 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i90 = load i32, i32* %size493, align 4
  %add494 = add nsw i32 %i90, %addsize.0
  %call495 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.2, i64 0, i64 0), i32 %add494)
  call void @exit(i32 1) #10
  unreachable

if.end496:                                        ; preds = %if.then481
  %sub497 = sub nsw i32 0, %decsize.0
  %conv498 = sext i32 %sub497 to i64
  %mul499 = mul i64 %conv498, 16
  %call500 = call i64 @quantum_memman(i64 %mul499)
  br label %if.end501

if.end501:                                        ; preds = %if.end496, %for.end479
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_hadamard(i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %m = alloca %struct.quantum_matrix_struct, align 8
  %tmp = alloca %struct.quantum_matrix_struct, align 8
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 6, i32 %target)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call { i64, { float, float }* } @quantum_new_matrix(i32 2, i32 2)
  %i = bitcast %struct.quantum_matrix_struct* %tmp to { i64, { float, float }* }*
  %i1 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 0
  %i2 = extractvalue { i64, { float, float }* } %call1, 0
  store i64 %i2, i64* %i1, align 8
  %i3 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 1
  %i4 = extractvalue { i64, { float, float }* } %call1, 1
  store { float, float }* %i4, { float, float }** %i3, align 8
  %i5 = bitcast %struct.quantum_matrix_struct* %m to i8*
  %i6 = bitcast %struct.quantum_matrix_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i5, i8* align 8 %i6, i64 16, i1 false)
  %call2 = call double @sqrt(double 5.000000e-01) #9
  %conv = fptrunc double %call2 to float
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i7 = load { float, float }*, { float, float }** %t, align 8
  %arrayidx = getelementptr inbounds { float, float }, { float, float }* %i7, i64 0
  %arrayidx.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 0
  %arrayidx.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 1
  store float %conv, float* %arrayidx.realp, align 4
  store float 0.000000e+00, float* %arrayidx.imagp, align 4
  %call3 = call double @sqrt(double 5.000000e-01) #9
  %conv4 = fptrunc double %call3 to float
  %t5 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i8 = load { float, float }*, { float, float }** %t5, align 8
  %arrayidx6 = getelementptr inbounds { float, float }, { float, float }* %i8, i64 1
  %arrayidx6.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx6, i32 0, i32 0
  %arrayidx6.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx6, i32 0, i32 1
  store float %conv4, float* %arrayidx6.realp, align 4
  store float 0.000000e+00, float* %arrayidx6.imagp, align 4
  %call7 = call double @sqrt(double 5.000000e-01) #9
  %conv8 = fptrunc double %call7 to float
  %t9 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i9 = load { float, float }*, { float, float }** %t9, align 8
  %arrayidx10 = getelementptr inbounds { float, float }, { float, float }* %i9, i64 2
  %arrayidx10.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx10, i32 0, i32 0
  %arrayidx10.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx10, i32 0, i32 1
  store float %conv8, float* %arrayidx10.realp, align 4
  store float 0.000000e+00, float* %arrayidx10.imagp, align 4
  %call11 = call double @sqrt(double 5.000000e-01) #9
  %fneg = fneg double %call11
  %conv12 = fptrunc double %fneg to float
  %t13 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i10 = load { float, float }*, { float, float }** %t13, align 8
  %arrayidx14 = getelementptr inbounds { float, float }, { float, float }* %i10, i64 3
  %arrayidx14.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx14, i32 0, i32 0
  %arrayidx14.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx14, i32 0, i32 1
  store float %conv12, float* %arrayidx14.realp, align 4
  store float 0.000000e+00, float* %arrayidx14.imagp, align 4
  %i11 = bitcast %struct.quantum_matrix_struct* %m to { i64, { float, float }* }*
  %i12 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i11, i32 0, i32 0
  %i13 = load i64, i64* %i12, align 8
  %i14 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i11, i32 0, i32 1
  %i15 = load { float, float }*, { float, float }** %i14, align 8
  call void @quantum_gate1(i32 %target, i64 %i13, { float, float }* %i15, %struct.quantum_reg_struct* %reg)
  call void @quantum_delete_matrix(%struct.quantum_matrix_struct* %m)
  br label %return

return:                                           ; preds = %if.end, %if.then
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #7

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_walsh(i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %i.0, %width
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  call void @quantum_hadamard(i32 %i.0, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_r_x(i32 %target, float %gamma, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %m = alloca %struct.quantum_matrix_struct, align 8
  %tmp = alloca %struct.quantum_matrix_struct, align 8
  %conv = fpext float %gamma to double
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 7, i32 %target, double %conv)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call { i64, { float, float }* } @quantum_new_matrix(i32 2, i32 2)
  %i = bitcast %struct.quantum_matrix_struct* %tmp to { i64, { float, float }* }*
  %i1 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 0
  %i2 = extractvalue { i64, { float, float }* } %call1, 0
  store i64 %i2, i64* %i1, align 8
  %i3 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 1
  %i4 = extractvalue { i64, { float, float }* } %call1, 1
  store { float, float }* %i4, { float, float }** %i3, align 8
  %i5 = bitcast %struct.quantum_matrix_struct* %m to i8*
  %i6 = bitcast %struct.quantum_matrix_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i5, i8* align 8 %i6, i64 16, i1 false)
  %div = fdiv float %gamma, 2.000000e+00
  %conv2 = fpext float %div to double
  %call3 = call double @cos(double %conv2) #9
  %conv4 = fptrunc double %call3 to float
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i7 = load { float, float }*, { float, float }** %t, align 8
  %arrayidx = getelementptr inbounds { float, float }, { float, float }* %i7, i64 0
  %arrayidx.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 0
  %arrayidx.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 1
  store float %conv4, float* %arrayidx.realp, align 4
  store float 0.000000e+00, float* %arrayidx.imagp, align 4
  %div5 = fdiv float %gamma, 2.000000e+00
  %conv6 = fpext float %div5 to double
  %call7 = call double @sin(double %conv6) #9
  %mul.rl = fmul double -0.000000e+00, %call7
  %mul.il = fmul double -1.000000e+00, %call7
  %conv8 = fptrunc double %mul.rl to float
  %conv9 = fptrunc double %mul.il to float
  %t10 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i8 = load { float, float }*, { float, float }** %t10, align 8
  %arrayidx11 = getelementptr inbounds { float, float }, { float, float }* %i8, i64 1
  %arrayidx11.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx11, i32 0, i32 0
  %arrayidx11.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx11, i32 0, i32 1
  store float %conv8, float* %arrayidx11.realp, align 4
  store float %conv9, float* %arrayidx11.imagp, align 4
  %div12 = fdiv float %gamma, 2.000000e+00
  %conv13 = fpext float %div12 to double
  %call14 = call double @sin(double %conv13) #9
  %mul.rl15 = fmul double -0.000000e+00, %call14
  %mul.il16 = fmul double -1.000000e+00, %call14
  %conv17 = fptrunc double %mul.rl15 to float
  %conv18 = fptrunc double %mul.il16 to float
  %t19 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i9 = load { float, float }*, { float, float }** %t19, align 8
  %arrayidx20 = getelementptr inbounds { float, float }, { float, float }* %i9, i64 2
  %arrayidx20.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx20, i32 0, i32 0
  %arrayidx20.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx20, i32 0, i32 1
  store float %conv17, float* %arrayidx20.realp, align 4
  store float %conv18, float* %arrayidx20.imagp, align 4
  %div21 = fdiv float %gamma, 2.000000e+00
  %conv22 = fpext float %div21 to double
  %call23 = call double @cos(double %conv22) #9
  %conv24 = fptrunc double %call23 to float
  %t25 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i10 = load { float, float }*, { float, float }** %t25, align 8
  %arrayidx26 = getelementptr inbounds { float, float }, { float, float }* %i10, i64 3
  %arrayidx26.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx26, i32 0, i32 0
  %arrayidx26.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx26, i32 0, i32 1
  store float %conv24, float* %arrayidx26.realp, align 4
  store float 0.000000e+00, float* %arrayidx26.imagp, align 4
  %i11 = bitcast %struct.quantum_matrix_struct* %m to { i64, { float, float }* }*
  %i12 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i11, i32 0, i32 0
  %i13 = load i64, i64* %i12, align 8
  %i14 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i11, i32 0, i32 1
  %i15 = load { float, float }*, { float, float }** %i14, align 8
  call void @quantum_gate1(i32 %target, i64 %i13, { float, float }* %i15, %struct.quantum_reg_struct* %reg)
  call void @quantum_delete_matrix(%struct.quantum_matrix_struct* %m)
  br label %return

return:                                           ; preds = %if.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_r_y(i32 %target, float %gamma, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %m = alloca %struct.quantum_matrix_struct, align 8
  %tmp = alloca %struct.quantum_matrix_struct, align 8
  %conv = fpext float %gamma to double
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 8, i32 %target, double %conv)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call { i64, { float, float }* } @quantum_new_matrix(i32 2, i32 2)
  %i = bitcast %struct.quantum_matrix_struct* %tmp to { i64, { float, float }* }*
  %i1 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 0
  %i2 = extractvalue { i64, { float, float }* } %call1, 0
  store i64 %i2, i64* %i1, align 8
  %i3 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 1
  %i4 = extractvalue { i64, { float, float }* } %call1, 1
  store { float, float }* %i4, { float, float }** %i3, align 8
  %i5 = bitcast %struct.quantum_matrix_struct* %m to i8*
  %i6 = bitcast %struct.quantum_matrix_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i5, i8* align 8 %i6, i64 16, i1 false)
  %div = fdiv float %gamma, 2.000000e+00
  %conv2 = fpext float %div to double
  %call3 = call double @cos(double %conv2) #9
  %conv4 = fptrunc double %call3 to float
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i7 = load { float, float }*, { float, float }** %t, align 8
  %arrayidx = getelementptr inbounds { float, float }, { float, float }* %i7, i64 0
  %arrayidx.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 0
  %arrayidx.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 1
  store float %conv4, float* %arrayidx.realp, align 4
  store float 0.000000e+00, float* %arrayidx.imagp, align 4
  %div5 = fdiv float %gamma, 2.000000e+00
  %conv6 = fpext float %div5 to double
  %call7 = call double @sin(double %conv6) #9
  %fneg = fneg double %call7
  %conv8 = fptrunc double %fneg to float
  %t9 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i8 = load { float, float }*, { float, float }** %t9, align 8
  %arrayidx10 = getelementptr inbounds { float, float }, { float, float }* %i8, i64 1
  %arrayidx10.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx10, i32 0, i32 0
  %arrayidx10.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx10, i32 0, i32 1
  store float %conv8, float* %arrayidx10.realp, align 4
  store float 0.000000e+00, float* %arrayidx10.imagp, align 4
  %div11 = fdiv float %gamma, 2.000000e+00
  %conv12 = fpext float %div11 to double
  %call13 = call double @sin(double %conv12) #9
  %conv14 = fptrunc double %call13 to float
  %t15 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i9 = load { float, float }*, { float, float }** %t15, align 8
  %arrayidx16 = getelementptr inbounds { float, float }, { float, float }* %i9, i64 2
  %arrayidx16.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx16, i32 0, i32 0
  %arrayidx16.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx16, i32 0, i32 1
  store float %conv14, float* %arrayidx16.realp, align 4
  store float 0.000000e+00, float* %arrayidx16.imagp, align 4
  %div17 = fdiv float %gamma, 2.000000e+00
  %conv18 = fpext float %div17 to double
  %call19 = call double @cos(double %conv18) #9
  %conv20 = fptrunc double %call19 to float
  %t21 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i10 = load { float, float }*, { float, float }** %t21, align 8
  %arrayidx22 = getelementptr inbounds { float, float }, { float, float }* %i10, i64 3
  %arrayidx22.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx22, i32 0, i32 0
  %arrayidx22.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx22, i32 0, i32 1
  store float %conv20, float* %arrayidx22.realp, align 4
  store float 0.000000e+00, float* %arrayidx22.imagp, align 4
  %i11 = bitcast %struct.quantum_matrix_struct* %m to { i64, { float, float }* }*
  %i12 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i11, i32 0, i32 0
  %i13 = load i64, i64* %i12, align 8
  %i14 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i11, i32 0, i32 1
  %i15 = load { float, float }*, { float, float }** %i14, align 8
  call void @quantum_gate1(i32 %target, i64 %i13, { float, float }* %i15, %struct.quantum_reg_struct* %reg)
  call void @quantum_delete_matrix(%struct.quantum_matrix_struct* %m)
  br label %return

return:                                           ; preds = %if.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_r_z(i32 %target, float %gamma, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %z = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce12 = alloca { float, float }, align 4
  %coerce24 = alloca { float, float }, align 4
  %conv = fpext float %gamma to double
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 9, i32 %target, double %conv)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %div = fdiv float %gamma, 2.000000e+00
  %call1 = call <2 x float> @quantum_cexp(float %div)
  %i = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call1, <2 x float>* %i, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %z.realp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.imagp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  store float %coerce.real, float* %z.realp, align 4
  store float %coerce.imag, float* %z.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %target to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i3, %shl
  %tobool3 = icmp ne i64 %and, 0
  br i1 %tobool3, label %if.then4, label %if.else

if.then4:                                         ; preds = %for.body
  %z.realp5 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real = load float, float* %z.realp5, align 4
  %z.imagp6 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag = load float, float* %z.imagp6, align 4
  %node7 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node7, align 8
  %idxprom8 = sext i32 %i.0 to i64
  %arrayidx9 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom8
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx9, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %z.real
  %mul_bd = fmul float %amplitude.imag, %z.imag
  %mul_ad = fmul float %amplitude.real, %z.imag
  %mul_bc = fmul float %amplitude.imag, %z.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then4
  %isnan_cmp10 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp10, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call11 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %z.real, float %z.imag) #9
  %i5 = bitcast { float, float }* %coerce12 to <2 x float>*
  store <2 x float> %call11, <2 x float>* %i5, align 4
  %coerce12.realp = getelementptr inbounds { float, float }, { float, float }* %coerce12, i32 0, i32 0
  %coerce12.real = load float, float* %coerce12.realp, align 4
  %coerce12.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce12, i32 0, i32 1
  %coerce12.imag = load float, float* %coerce12.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then4
  %real_mul_phi = phi float [ %mul_r, %if.then4 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce12.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then4 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce12.imag, %complex_mul_libcall ]
  %amplitude.realp13 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp14 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp13, align 8
  store float %imag_mul_phi, float* %amplitude.imagp14, align 4
  br label %if.end27

if.else:                                          ; preds = %for.body
  %z.realp15 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real16 = load float, float* %z.realp15, align 4
  %z.imagp17 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag18 = load float, float* %z.imagp17, align 4
  %node19 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node19, align 8
  %idxprom20 = sext i32 %i.0 to i64
  %arrayidx21 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom20
  %amplitude22 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx21, i32 0, i32 0
  %amplitude22.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude22, i32 0, i32 0
  %amplitude22.real = load float, float* %amplitude22.realp, align 8
  %amplitude22.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude22, i32 0, i32 1
  %amplitude22.imag = load float, float* %amplitude22.imagp, align 4
  %call23 = call <2 x float> @__divsc3(float %amplitude22.real, float %amplitude22.imag, float %z.real16, float %z.imag18) #9
  %i7 = bitcast { float, float }* %coerce24 to <2 x float>*
  store <2 x float> %call23, <2 x float>* %i7, align 4
  %coerce24.realp = getelementptr inbounds { float, float }, { float, float }* %coerce24, i32 0, i32 0
  %coerce24.real = load float, float* %coerce24.realp, align 4
  %coerce24.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce24, i32 0, i32 1
  %coerce24.imag = load float, float* %coerce24.imagp, align 4
  %amplitude22.realp25 = getelementptr inbounds { float, float }, { float, float }* %amplitude22, i32 0, i32 0
  %amplitude22.imagp26 = getelementptr inbounds { float, float }, { float, float }* %amplitude22, i32 0, i32 1
  store float %coerce24.real, float* %amplitude22.realp25, align 8
  store float %coerce24.imag, float* %amplitude22.imagp26, align 4
  br label %if.end27

if.end27:                                         ; preds = %if.else, %complex_mul_cont
  br label %for.inc

for.inc:                                          ; preds = %if.end27
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

declare dso_local <2 x float> @__divsc3(float, float, float, float)

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_phase_scale(i32 %target, float %gamma, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %z = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce7 = alloca { float, float }, align 4
  %conv = fpext float %gamma to double
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 11, i32 %target, double %conv)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call <2 x float> @quantum_cexp(float %gamma)
  %i = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call1, <2 x float>* %i, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %z.realp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.imagp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  store float %coerce.real, float* %z.realp, align 4
  store float %coerce.imag, float* %z.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %z.realp3 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real = load float, float* %z.realp3, align 4
  %z.imagp4 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag = load float, float* %z.imagp4, align 4
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %z.real
  %mul_bd = fmul float %amplitude.imag, %z.imag
  %mul_ad = fmul float %amplitude.real, %z.imag
  %mul_bc = fmul float %amplitude.imag, %z.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %for.body
  %isnan_cmp5 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp5, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call6 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %z.real, float %z.imag) #9
  %i3 = bitcast { float, float }* %coerce7 to <2 x float>*
  store <2 x float> %call6, <2 x float>* %i3, align 4
  %coerce7.realp = getelementptr inbounds { float, float }, { float, float }* %coerce7, i32 0, i32 0
  %coerce7.real = load float, float* %coerce7.realp, align 4
  %coerce7.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce7, i32 0, i32 1
  %coerce7.imag = load float, float* %coerce7.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %for.body
  %real_mul_phi = phi float [ %mul_r, %for.body ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce7.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %for.body ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce7.imag, %complex_mul_libcall ]
  %amplitude.realp8 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp9 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp8, align 8
  store float %imag_mul_phi, float* %amplitude.imagp9, align 4
  br label %for.inc

for.inc:                                          ; preds = %complex_mul_cont
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_phase_kick(i32 %target, float %gamma, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %z = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce12 = alloca { float, float }, align 4
  %conv = fpext float %gamma to double
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 10, i32 %target, double %conv)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call <2 x float> @quantum_cexp(float %gamma)
  %i = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call1, <2 x float>* %i, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %z.realp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.imagp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  store float %coerce.real, float* %z.realp, align 4
  store float %coerce.imag, float* %z.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %target to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i3, %shl
  %tobool3 = icmp ne i64 %and, 0
  br i1 %tobool3, label %if.then4, label %if.end15

if.then4:                                         ; preds = %for.body
  %z.realp5 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real = load float, float* %z.realp5, align 4
  %z.imagp6 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag = load float, float* %z.imagp6, align 4
  %node7 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node7, align 8
  %idxprom8 = sext i32 %i.0 to i64
  %arrayidx9 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom8
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx9, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %z.real
  %mul_bd = fmul float %amplitude.imag, %z.imag
  %mul_ad = fmul float %amplitude.real, %z.imag
  %mul_bc = fmul float %amplitude.imag, %z.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then4
  %isnan_cmp10 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp10, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call11 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %z.real, float %z.imag) #9
  %i5 = bitcast { float, float }* %coerce12 to <2 x float>*
  store <2 x float> %call11, <2 x float>* %i5, align 4
  %coerce12.realp = getelementptr inbounds { float, float }, { float, float }* %coerce12, i32 0, i32 0
  %coerce12.real = load float, float* %coerce12.realp, align 4
  %coerce12.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce12, i32 0, i32 1
  %coerce12.imag = load float, float* %coerce12.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then4
  %real_mul_phi = phi float [ %mul_r, %if.then4 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce12.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then4 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce12.imag, %complex_mul_libcall ]
  %amplitude.realp13 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp14 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp13, align 8
  store float %imag_mul_phi, float* %amplitude.imagp14, align 4
  br label %if.end15

if.end15:                                         ; preds = %complex_mul_cont, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end15
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_cond_phase(i32 %control, i32 %target, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %z = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce24 = alloca { float, float }, align 4
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 12, i32 %control, i32 %target)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %sub = sub nsw i32 %control, %target
  %sh_prom = zext i32 %sub to i64
  %shl = shl i64 1, %sh_prom
  %conv = uitofp i64 %shl to double
  %div = fdiv double 0x400921FB54524550, %conv
  %conv1 = fptrunc double %div to float
  %call2 = call <2 x float> @quantum_cexp(float %conv1)
  %i = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call2, <2 x float>* %i, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %z.realp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.imagp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  store float %coerce.real, float* %z.realp, align 4
  store float %coerce.imag, float* %z.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom4 = zext i32 %control to i64
  %shl5 = shl i64 1, %sh_prom4
  %and = and i64 %i3, %shl5
  %tobool6 = icmp ne i64 %and, 0
  br i1 %tobool6, label %if.then7, label %if.end28

if.then7:                                         ; preds = %for.body
  %node8 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node8, align 8
  %idxprom9 = sext i32 %i.0 to i64
  %arrayidx10 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom9
  %state11 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx10, i32 0, i32 1
  %i5 = load i64, i64* %state11, align 8
  %sh_prom12 = zext i32 %target to i64
  %shl13 = shl i64 1, %sh_prom12
  %and14 = and i64 %i5, %shl13
  %tobool15 = icmp ne i64 %and14, 0
  br i1 %tobool15, label %if.then16, label %if.end27

if.then16:                                        ; preds = %if.then7
  %z.realp17 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real = load float, float* %z.realp17, align 4
  %z.imagp18 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag = load float, float* %z.imagp18, align 4
  %node19 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node19, align 8
  %idxprom20 = sext i32 %i.0 to i64
  %arrayidx21 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom20
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx21, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %z.real
  %mul_bd = fmul float %amplitude.imag, %z.imag
  %mul_ad = fmul float %amplitude.real, %z.imag
  %mul_bc = fmul float %amplitude.imag, %z.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then16
  %isnan_cmp22 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp22, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call23 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %z.real, float %z.imag) #9
  %i7 = bitcast { float, float }* %coerce24 to <2 x float>*
  store <2 x float> %call23, <2 x float>* %i7, align 4
  %coerce24.realp = getelementptr inbounds { float, float }, { float, float }* %coerce24, i32 0, i32 0
  %coerce24.real = load float, float* %coerce24.realp, align 4
  %coerce24.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce24, i32 0, i32 1
  %coerce24.imag = load float, float* %coerce24.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then16
  %real_mul_phi = phi float [ %mul_r, %if.then16 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce24.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then16 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce24.imag, %complex_mul_libcall ]
  %amplitude.realp25 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp26 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp25, align 8
  store float %imag_mul_phi, float* %amplitude.imagp26, align 4
  br label %if.end27

if.end27:                                         ; preds = %complex_mul_cont, %if.then7
  br label %if.end28

if.end28:                                         ; preds = %if.end27, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end28
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_cond_phase_inv(i32 %control, i32 %target, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %z = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce21 = alloca { float, float }, align 4
  %sub = sub nsw i32 %control, %target
  %sh_prom = zext i32 %sub to i64
  %shl = shl i64 1, %sh_prom
  %conv = uitofp i64 %shl to double
  %div = fdiv double 0xC00921FB54524550, %conv
  %conv1 = fptrunc double %div to float
  %call = call <2 x float> @quantum_cexp(float %conv1)
  %i = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call, <2 x float>* %i, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %z.realp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.imagp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  store float %coerce.real, float* %z.realp, align 4
  store float %coerce.imag, float* %z.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom3 = zext i32 %control to i64
  %shl4 = shl i64 1, %sh_prom3
  %and = and i64 %i3, %shl4
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %if.then, label %if.end24

if.then:                                          ; preds = %for.body
  %node5 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node5, align 8
  %idxprom6 = sext i32 %i.0 to i64
  %arrayidx7 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom6
  %state8 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx7, i32 0, i32 1
  %i5 = load i64, i64* %state8, align 8
  %sh_prom9 = zext i32 %target to i64
  %shl10 = shl i64 1, %sh_prom9
  %and11 = and i64 %i5, %shl10
  %tobool12 = icmp ne i64 %and11, 0
  br i1 %tobool12, label %if.then13, label %if.end

if.then13:                                        ; preds = %if.then
  %z.realp14 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real = load float, float* %z.realp14, align 4
  %z.imagp15 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag = load float, float* %z.imagp15, align 4
  %node16 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node16, align 8
  %idxprom17 = sext i32 %i.0 to i64
  %arrayidx18 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom17
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx18, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %z.real
  %mul_bd = fmul float %amplitude.imag, %z.imag
  %mul_ad = fmul float %amplitude.real, %z.imag
  %mul_bc = fmul float %amplitude.imag, %z.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then13
  %isnan_cmp19 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp19, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call20 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %z.real, float %z.imag) #9
  %i7 = bitcast { float, float }* %coerce21 to <2 x float>*
  store <2 x float> %call20, <2 x float>* %i7, align 4
  %coerce21.realp = getelementptr inbounds { float, float }, { float, float }* %coerce21, i32 0, i32 0
  %coerce21.real = load float, float* %coerce21.realp, align 4
  %coerce21.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce21, i32 0, i32 1
  %coerce21.imag = load float, float* %coerce21.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then13
  %real_mul_phi = phi float [ %mul_r, %if.then13 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce21.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then13 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce21.imag, %complex_mul_libcall ]
  %amplitude.realp22 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp23 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp22, align 8
  store float %imag_mul_phi, float* %amplitude.imagp23, align 4
  br label %if.end

if.end:                                           ; preds = %complex_mul_cont, %if.then
  br label %if.end24

if.end24:                                         ; preds = %if.end, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end24
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_cond_phase_kick(i32 %control, i32 %target, float %gamma, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %z = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce21 = alloca { float, float }, align 4
  %conv = fpext float %gamma to double
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 12, i32 %control, i32 %target, double %conv)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call <2 x float> @quantum_cexp(float %gamma)
  %i = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call1, <2 x float>* %i, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  %z.realp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.imagp = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  store float %coerce.real, float* %z.realp, align 4
  store float %coerce.imag, float* %z.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i1 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i1
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i2 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i2, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i3 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %control to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %i3, %shl
  %tobool3 = icmp ne i64 %and, 0
  br i1 %tobool3, label %if.then4, label %if.end25

if.then4:                                         ; preds = %for.body
  %node5 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node5, align 8
  %idxprom6 = sext i32 %i.0 to i64
  %arrayidx7 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom6
  %state8 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx7, i32 0, i32 1
  %i5 = load i64, i64* %state8, align 8
  %sh_prom9 = zext i32 %target to i64
  %shl10 = shl i64 1, %sh_prom9
  %and11 = and i64 %i5, %shl10
  %tobool12 = icmp ne i64 %and11, 0
  br i1 %tobool12, label %if.then13, label %if.end24

if.then13:                                        ; preds = %if.then4
  %z.realp14 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 0
  %z.real = load float, float* %z.realp14, align 4
  %z.imagp15 = getelementptr inbounds { float, float }, { float, float }* %z, i32 0, i32 1
  %z.imag = load float, float* %z.imagp15, align 4
  %node16 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node16, align 8
  %idxprom17 = sext i32 %i.0 to i64
  %arrayidx18 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom17
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx18, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %z.real
  %mul_bd = fmul float %amplitude.imag, %z.imag
  %mul_ad = fmul float %amplitude.real, %z.imag
  %mul_bc = fmul float %amplitude.imag, %z.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then13
  %isnan_cmp19 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp19, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call20 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %z.real, float %z.imag) #9
  %i7 = bitcast { float, float }* %coerce21 to <2 x float>*
  store <2 x float> %call20, <2 x float>* %i7, align 4
  %coerce21.realp = getelementptr inbounds { float, float }, { float, float }* %coerce21, i32 0, i32 0
  %coerce21.real = load float, float* %coerce21.realp, align 4
  %coerce21.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce21, i32 0, i32 1
  %coerce21.imag = load float, float* %coerce21.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then13
  %real_mul_phi = phi float [ %mul_r, %if.then13 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce21.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then13 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce21.imag, %complex_mul_libcall ]
  %amplitude.realp22 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp23 = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude.realp22, align 8
  store float %imag_mul_phi, float* %amplitude.imagp23, align 4
  br label %if.end24

if.end24:                                         ; preds = %complex_mul_cont, %if.then4
  br label %if.end25

if.end25:                                         ; preds = %if.end24, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end25
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  br label %return

return:                                           ; preds = %for.end, %if.then
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_gate_counter(i32 %inc) #0 {
entry:
  %cmp = icmp sgt i32 %inc, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i = load i32, i32* @quantum_gate_counter.counter, align 4
  %add = add nsw i32 %i, %inc
  store i32 %add, i32* @quantum_gate_counter.counter, align 4
  br label %if.end3

if.else:                                          ; preds = %entry
  %cmp1 = icmp slt i32 %inc, 0
  br i1 %cmp1, label %if.then2, label %if.end

if.then2:                                         ; preds = %if.else
  store i32 0, i32* @quantum_gate_counter.counter, align 4
  br label %if.end

if.end:                                           ; preds = %if.then2, %if.else
  br label %if.end3

if.end3:                                          ; preds = %if.end, %if.then
  %i1 = load i32, i32* @quantum_gate_counter.counter, align 4
  ret i32 %i1
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @quantum_memman(i64 %change) #0 {
entry:
  %i = load i64, i64* @quantum_memman.mem, align 8
  %add = add nsw i64 %i, %change
  store i64 %add, i64* @quantum_memman.mem, align 8
  %i1 = load i64, i64* @quantum_memman.mem, align 8
  %i2 = load i64, i64* @quantum_memman.max, align 8
  %cmp = icmp sgt i64 %i1, %i2
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i3 = load i64, i64* @quantum_memman.mem, align 8
  store i64 %i3, i64* @quantum_memman.max, align 8
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %i4 = load i64, i64* @quantum_memman.mem, align 8
  ret i64 %i4
}

; Function Attrs: noinline nounwind uwtable
define dso_local { i64, { float, float }* } @quantum_new_matrix(i32 %cols, i32 %rows) #0 {
entry:
  %retval = alloca %struct.quantum_matrix_struct, align 8
  %rows1 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %retval, i32 0, i32 0
  store i32 %rows, i32* %rows1, align 8
  %cols2 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %retval, i32 0, i32 1
  store i32 %cols, i32* %cols2, align 4
  %mul = mul nsw i32 %cols, %rows
  %conv = sext i32 %mul to i64
  %call = call noalias i8* @calloc(i64 %conv, i64 8) #9
  %i = bitcast i8* %call to { float, float }*
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %retval, i32 0, i32 2
  store { float, float }* %i, { float, float }** %t, align 8
  %t3 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %retval, i32 0, i32 2
  %i1 = load { float, float }*, { float, float }** %t3, align 8
  %tobool = icmp ne { float, float }* %i1, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %call4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.14, i64 0, i64 0), i32 %rows, i32 %cols)
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %entry
  %conv5 = sext i32 %cols to i64
  %mul6 = mul i64 8, %conv5
  %conv7 = sext i32 %rows to i64
  %mul8 = mul i64 %mul6, %conv7
  %call9 = call i64 @quantum_memman(i64 %mul8)
  %i2 = bitcast %struct.quantum_matrix_struct* %retval to { i64, { float, float }* }*
  %i3 = load { i64, { float, float }* }, { i64, { float, float }* }* %i2, align 8
  ret { i64, { float, float }* } %i3
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_delete_matrix(%struct.quantum_matrix_struct* %m) #0 {
entry:
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i = load { float, float }*, { float, float }** %t, align 8
  %i1 = bitcast { float, float }* %i to i8*
  call void @free(i8* %i1) #9
  %cols = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i2 = load i32, i32* %cols, align 4
  %conv = sext i32 %i2 to i64
  %mul = mul i64 -8, %conv
  %rows = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i3 = load i32, i32* %rows, align 8
  %conv1 = sext i32 %i3 to i64
  %mul2 = mul i64 %mul, %conv1
  %call = call i64 @quantum_memman(i64 %mul2)
  %t3 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  store { float, float }* null, { float, float }** %t3, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_print_matrix(i64 %m.coerce0, { float, float }* %m.coerce1) #2 {
entry:
  %m = alloca %struct.quantum_matrix_struct, align 8
  %coerce = alloca { float, float }, align 4
  %coerce13 = alloca { float, float }, align 4
  %i = bitcast %struct.quantum_matrix_struct* %m to { i64, { float, float }* }*
  %i1 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 0
  store i64 %m.coerce0, i64* %i1, align 8
  %i2 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i, i32 0, i32 1
  store { float, float }* %m.coerce1, { float, float }** %i2, align 8
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %z.0 = phi i32 [ 0, %entry ], [ %inc, %while.body ]
  %inc = add nsw i32 %z.0, 1
  %shl = shl i32 1, %z.0
  %rows = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i3 = load i32, i32* %rows, align 8
  %cmp = icmp slt i32 %shl, %i3
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %dec = add nsw i32 %inc, -1
  br label %for.cond

for.cond:                                         ; preds = %for.inc19, %while.end
  %i.0 = phi i32 [ 0, %while.end ], [ %inc20, %for.inc19 ]
  %rows1 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i4 = load i32, i32* %rows1, align 8
  %cmp2 = icmp slt i32 %i.0, %i4
  br i1 %cmp2, label %for.body, label %for.end21

for.body:                                         ; preds = %for.cond
  br label %for.cond3

for.cond3:                                        ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ 0, %for.body ], [ %inc17, %for.inc ]
  %cols = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i5 = load i32, i32* %cols, align 4
  %cmp4 = icmp slt i32 %j.0, %i5
  br i1 %cmp4, label %for.body5, label %for.end

for.body5:                                        ; preds = %for.cond3
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i6 = load { float, float }*, { float, float }** %t, align 8
  %cols6 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i7 = load i32, i32* %cols6, align 4
  %mul = mul nsw i32 %i.0, %i7
  %add = add nsw i32 %j.0, %mul
  %idxprom = sext i32 %add to i64
  %arrayidx = getelementptr inbounds { float, float }, { float, float }* %i6, i64 %idxprom
  %arrayidx.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 0
  %arrayidx.real = load float, float* %arrayidx.realp, align 4
  %arrayidx.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 1
  %arrayidx.imag = load float, float* %arrayidx.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %arrayidx.real, float* %coerce.realp, align 4
  store float %arrayidx.imag, float* %coerce.imagp, align 4
  %i8 = bitcast { float, float }* %coerce to <2 x float>*
  %i9 = load <2 x float>, <2 x float>* %i8, align 4
  %call = call float @quantum_real.17(<2 x float> %i9)
  %conv = fpext float %call to double
  %t7 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i10 = load { float, float }*, { float, float }** %t7, align 8
  %cols8 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i11 = load i32, i32* %cols8, align 4
  %mul9 = mul nsw i32 %i.0, %i11
  %add10 = add nsw i32 %j.0, %mul9
  %idxprom11 = sext i32 %add10 to i64
  %arrayidx12 = getelementptr inbounds { float, float }, { float, float }* %i10, i64 %idxprom11
  %arrayidx12.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx12, i32 0, i32 0
  %arrayidx12.real = load float, float* %arrayidx12.realp, align 4
  %arrayidx12.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx12, i32 0, i32 1
  %arrayidx12.imag = load float, float* %arrayidx12.imagp, align 4
  %coerce13.realp = getelementptr inbounds { float, float }, { float, float }* %coerce13, i32 0, i32 0
  %coerce13.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce13, i32 0, i32 1
  store float %arrayidx12.real, float* %coerce13.realp, align 4
  store float %arrayidx12.imag, float* %coerce13.imagp, align 4
  %i12 = bitcast { float, float }* %coerce13 to <2 x float>*
  %i13 = load <2 x float>, <2 x float>* %i12, align 4
  %call14 = call float @quantum_imag.18(<2 x float> %i13)
  %conv15 = fpext float %call14 to double
  %call16 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.1.19, i64 0, i64 0), double %conv, double %conv15)
  br label %for.inc

for.inc:                                          ; preds = %for.body5
  %inc17 = add nsw i32 %j.0, 1
  br label %for.cond3

for.end:                                          ; preds = %for.cond3
  %call18 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2.20, i64 0, i64 0))
  br label %for.inc19

for.inc19:                                        ; preds = %for.end
  %inc20 = add nsw i32 %i.0, 1
  br label %for.cond

for.end21:                                        ; preds = %for.cond
  %call22 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2.20, i64 0, i64 0))
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_real.17(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 0
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_imag.18(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 1
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define dso_local double @quantum_frand() #0 {
entry:
  %call = call double @spec_rand()
  ret double %call
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @quantum_measure(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext -128)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call1 = call double @quantum_frand()
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %r.0 = phi double [ %call1, %if.end ], [ %sub, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %amplitude.real, float* %coerce.realp, align 4
  store float %amplitude.imag, float* %coerce.imagp, align 4
  %i2 = bitcast { float, float }* %coerce to <2 x float>*
  %i3 = load <2 x float>, <2 x float>* %i2, align 4
  %call2 = call float @quantum_prob_inline.23(<2 x float> %i3)
  %conv = fpext float %call2 to double
  %sub = fsub double %r.0, %conv
  %cmp3 = fcmp oge double 0.000000e+00, %sub
  br i1 %cmp3, label %if.then5, label %if.end9

if.then5:                                         ; preds = %for.body
  %node6 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node6, align 8
  %idxprom7 = sext i32 %i.0 to i64
  %arrayidx8 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom7
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx8, i32 0, i32 1
  %i5 = load i64, i64* %state, align 8
  br label %return

if.end9:                                          ; preds = %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end9
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %return

return:                                           ; preds = %for.end, %if.then5, %if.then
  %retval.0 = phi i64 [ 0, %if.then ], [ %i5, %if.then5 ], [ -1, %for.end ]
  ret i64 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_prob_inline.23(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce5 = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %a.realp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real = load float, float* %a.realp, align 4
  %a.imagp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag = load float, float* %a.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %a.real, float* %coerce.realp, align 4
  store float %a.imag, float* %coerce.imagp, align 4
  %i1 = bitcast { float, float }* %coerce to <2 x float>*
  %i2 = load <2 x float>, <2 x float>* %i1, align 4
  %call = call float @quantum_real.24(<2 x float> %i2)
  %a.realp1 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real2 = load float, float* %a.realp1, align 4
  %a.imagp3 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag4 = load float, float* %a.imagp3, align 4
  %coerce5.realp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 0
  %coerce5.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 1
  store float %a.real2, float* %coerce5.realp, align 4
  store float %a.imag4, float* %coerce5.imagp, align 4
  %i3 = bitcast { float, float }* %coerce5 to <2 x float>*
  %i4 = load <2 x float>, <2 x float>* %i3, align 4
  %call6 = call float @quantum_imag.25(<2 x float> %i4)
  %mul = fmul float %call, %call
  %mul7 = fmul float %call6, %call6
  %add = fadd float %mul, %mul7
  ret float %add
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_real.24(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 0
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_imag.25(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 1
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_bmeasure(i32 %pos, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %out = alloca %struct.quantum_reg_struct, align 8
  %coerce = alloca { float, float }, align 4
  %tmp = alloca %struct.quantum_reg_struct, align 8
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext -127, i32 %pos)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %sh_prom = zext i32 %pos to i64
  %shl = shl i64 1, %sh_prom
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %pa.0 = phi double [ 0.000000e+00, %if.end ], [ %pa.1, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i2 = load i64, i64* %state, align 8
  %and = and i64 %i2, %shl
  %tobool1 = icmp ne i64 %and, 0
  br i1 %tobool1, label %if.end7, label %if.then2

if.then2:                                         ; preds = %for.body
  %node3 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node3, align 8
  %idxprom4 = sext i32 %i.0 to i64
  %arrayidx5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom4
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx5, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %amplitude.real, float* %coerce.realp, align 4
  store float %amplitude.imag, float* %coerce.imagp, align 4
  %i4 = bitcast { float, float }* %coerce to <2 x float>*
  %i5 = load <2 x float>, <2 x float>* %i4, align 4
  %call6 = call float @quantum_prob_inline.23(<2 x float> %i5)
  %conv = fpext float %call6 to double
  %add = fadd double %pa.0, %conv
  br label %if.end7

if.end7:                                          ; preds = %if.then2, %for.body
  %pa.1 = phi double [ %pa.0, %for.body ], [ %add, %if.then2 ]
  br label %for.inc

for.inc:                                          ; preds = %if.end7
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %call8 = call double @quantum_frand()
  %cmp9 = fcmp ogt double %call8, %pa.0
  br i1 %cmp9, label %if.then11, label %if.end12

if.then11:                                        ; preds = %for.end
  br label %if.end12

if.end12:                                         ; preds = %if.then11, %for.end
  %result.0 = phi i32 [ 1, %if.then11 ], [ 0, %for.end ]
  call void @quantum_state_collapse(%struct.quantum_reg_struct* sret(%struct.quantum_reg_struct) align 8 %tmp, i32 %pos, i32 %result.0, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg)
  %i6 = bitcast %struct.quantum_reg_struct* %out to i8*
  %i7 = bitcast %struct.quantum_reg_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i6, i8* align 8 %i7, i64 32, i1 false)
  call void @quantum_delete_qureg_hashpreserve(%struct.quantum_reg_struct* %reg)
  %i8 = bitcast %struct.quantum_reg_struct* %reg to i8*
  %i9 = bitcast %struct.quantum_reg_struct* %out to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i8, i8* align 8 %i9, i64 32, i1 false)
  br label %return

return:                                           ; preds = %if.end12, %if.then
  %retval.0 = phi i32 [ 0, %if.then ], [ %result.0, %if.end12 ]
  ret i32 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_bmeasure_bitpreserve(i32 %pos, %struct.quantum_reg_struct* %reg) #2 {
entry:
  %out = alloca %struct.quantum_reg_struct, align 8
  %coerce = alloca { float, float }, align 4
  %coerce36 = alloca { float, float }, align 4
  %coerce54 = alloca { float, float }, align 4
  %coerce105 = alloca { float, float }, align 4
  %call = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext -126, i32 %pos)
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %sh_prom = zext i32 %pos to i64
  %shl = shl i64 1, %sh_prom
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc, %for.inc ]
  %pa.0 = phi double [ 0.000000e+00, %if.end ], [ %pa.1, %for.inc ]
  %size1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size1, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i2 = load i64, i64* %state, align 8
  %and = and i64 %i2, %shl
  %tobool2 = icmp ne i64 %and, 0
  br i1 %tobool2, label %if.end8, label %if.then3

if.then3:                                         ; preds = %for.body
  %node4 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node4, align 8
  %idxprom5 = sext i32 %i.0 to i64
  %arrayidx6 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom5
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx6, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %amplitude.real, float* %coerce.realp, align 4
  store float %amplitude.imag, float* %coerce.imagp, align 4
  %i4 = bitcast { float, float }* %coerce to <2 x float>*
  %i5 = load <2 x float>, <2 x float>* %i4, align 4
  %call7 = call float @quantum_prob_inline.23(<2 x float> %i5)
  %conv = fpext float %call7 to double
  %add = fadd double %pa.0, %conv
  br label %if.end8

if.end8:                                          ; preds = %if.then3, %for.body
  %pa.1 = phi double [ %pa.0, %for.body ], [ %add, %if.then3 ]
  br label %for.inc

for.inc:                                          ; preds = %if.end8
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %call9 = call double @quantum_frand()
  %cmp10 = fcmp ogt double %call9, %pa.0
  br i1 %cmp10, label %if.then12, label %if.end13

if.then12:                                        ; preds = %for.end
  br label %if.end13

if.end13:                                         ; preds = %if.then12, %for.end
  %result.0 = phi i32 [ 1, %if.then12 ], [ 0, %for.end ]
  br label %for.cond14

for.cond14:                                       ; preds = %for.inc61, %if.end13
  %size.0 = phi i32 [ 0, %if.end13 ], [ %size.3, %for.inc61 ]
  %i.1 = phi i32 [ 0, %if.end13 ], [ %inc62, %for.inc61 ]
  %d.0 = phi double [ 0.000000e+00, %if.end13 ], [ %d.3, %for.inc61 ]
  %size15 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i6 = load i32, i32* %size15, align 4
  %cmp16 = icmp slt i32 %i.1, %i6
  br i1 %cmp16, label %for.body18, label %for.end63

for.body18:                                       ; preds = %for.cond14
  %node19 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i7 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node19, align 8
  %idxprom20 = sext i32 %i.1 to i64
  %arrayidx21 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i7, i64 %idxprom20
  %state22 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx21, i32 0, i32 1
  %i8 = load i64, i64* %state22, align 8
  %and23 = and i64 %i8, %shl
  %tobool24 = icmp ne i64 %and23, 0
  br i1 %tobool24, label %if.then25, label %if.else42

if.then25:                                        ; preds = %for.body18
  %tobool26 = icmp ne i32 %result.0, 0
  br i1 %tobool26, label %if.else, label %if.then27

if.then27:                                        ; preds = %if.then25
  %node28 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i9 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node28, align 8
  %idxprom29 = sext i32 %i.1 to i64
  %arrayidx30 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i9, i64 %idxprom29
  %amplitude31 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx30, i32 0, i32 0
  %amplitude31.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude31, i32 0, i32 0
  %amplitude31.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude31, i32 0, i32 1
  store float 0.000000e+00, float* %amplitude31.realp, align 8
  store float 0.000000e+00, float* %amplitude31.imagp, align 4
  br label %if.end41

if.else:                                          ; preds = %if.then25
  %node32 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i10 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node32, align 8
  %idxprom33 = sext i32 %i.1 to i64
  %arrayidx34 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i10, i64 %idxprom33
  %amplitude35 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx34, i32 0, i32 0
  %amplitude35.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude35, i32 0, i32 0
  %amplitude35.real = load float, float* %amplitude35.realp, align 8
  %amplitude35.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude35, i32 0, i32 1
  %amplitude35.imag = load float, float* %amplitude35.imagp, align 4
  %coerce36.realp = getelementptr inbounds { float, float }, { float, float }* %coerce36, i32 0, i32 0
  %coerce36.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce36, i32 0, i32 1
  store float %amplitude35.real, float* %coerce36.realp, align 4
  store float %amplitude35.imag, float* %coerce36.imagp, align 4
  %i11 = bitcast { float, float }* %coerce36 to <2 x float>*
  %i12 = load <2 x float>, <2 x float>* %i11, align 4
  %call37 = call float @quantum_prob_inline.23(<2 x float> %i12)
  %conv38 = fpext float %call37 to double
  %add39 = fadd double %d.0, %conv38
  %inc40 = add nsw i32 %size.0, 1
  br label %if.end41

if.end41:                                         ; preds = %if.else, %if.then27
  %size.1 = phi i32 [ %inc40, %if.else ], [ %size.0, %if.then27 ]
  %d.1 = phi double [ %add39, %if.else ], [ %d.0, %if.then27 ]
  br label %if.end60

if.else42:                                        ; preds = %for.body18
  %tobool43 = icmp ne i32 %result.0, 0
  br i1 %tobool43, label %if.then44, label %if.else49

if.then44:                                        ; preds = %if.else42
  %node45 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i13 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node45, align 8
  %idxprom46 = sext i32 %i.1 to i64
  %arrayidx47 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i13, i64 %idxprom46
  %amplitude48 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx47, i32 0, i32 0
  %amplitude48.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude48, i32 0, i32 0
  %amplitude48.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude48, i32 0, i32 1
  store float 0.000000e+00, float* %amplitude48.realp, align 8
  store float 0.000000e+00, float* %amplitude48.imagp, align 4
  br label %if.end59

if.else49:                                        ; preds = %if.else42
  %node50 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i14 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node50, align 8
  %idxprom51 = sext i32 %i.1 to i64
  %arrayidx52 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i14, i64 %idxprom51
  %amplitude53 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx52, i32 0, i32 0
  %amplitude53.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude53, i32 0, i32 0
  %amplitude53.real = load float, float* %amplitude53.realp, align 8
  %amplitude53.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude53, i32 0, i32 1
  %amplitude53.imag = load float, float* %amplitude53.imagp, align 4
  %coerce54.realp = getelementptr inbounds { float, float }, { float, float }* %coerce54, i32 0, i32 0
  %coerce54.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce54, i32 0, i32 1
  store float %amplitude53.real, float* %coerce54.realp, align 4
  store float %amplitude53.imag, float* %coerce54.imagp, align 4
  %i15 = bitcast { float, float }* %coerce54 to <2 x float>*
  %i16 = load <2 x float>, <2 x float>* %i15, align 4
  %call55 = call float @quantum_prob_inline.23(<2 x float> %i16)
  %conv56 = fpext float %call55 to double
  %add57 = fadd double %d.0, %conv56
  %inc58 = add nsw i32 %size.0, 1
  br label %if.end59

if.end59:                                         ; preds = %if.else49, %if.then44
  %size.2 = phi i32 [ %size.0, %if.then44 ], [ %inc58, %if.else49 ]
  %d.2 = phi double [ %d.0, %if.then44 ], [ %add57, %if.else49 ]
  br label %if.end60

if.end60:                                         ; preds = %if.end59, %if.end41
  %size.3 = phi i32 [ %size.1, %if.end41 ], [ %size.2, %if.end59 ]
  %d.3 = phi double [ %d.1, %if.end41 ], [ %d.2, %if.end59 ]
  br label %for.inc61

for.inc61:                                        ; preds = %if.end60
  %inc62 = add nsw i32 %i.1, 1
  br label %for.cond14

for.end63:                                        ; preds = %for.cond14
  %size64 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 1
  store i32 %size.0, i32* %size64, align 4
  %conv65 = sext i32 %size.0 to i64
  %call66 = call noalias i8* @calloc(i64 %conv65, i64 16) #9
  %i17 = bitcast i8* %call66 to %struct.quantum_reg_node_struct*
  %node67 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i17, %struct.quantum_reg_node_struct** %node67, align 8
  %node68 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 3
  %i18 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node68, align 8
  %tobool69 = icmp ne %struct.quantum_reg_node_struct* %i18, null
  br i1 %tobool69, label %if.end72, label %if.then70

if.then70:                                        ; preds = %for.end63
  %call71 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.26, i64 0, i64 0), i32 %size.0)
  call void @exit(i32 1) #10
  unreachable

if.end72:                                         ; preds = %for.end63
  %conv73 = sext i32 %size.0 to i64
  %mul = mul i64 %conv73, 16
  %call74 = call i64 @quantum_memman(i64 %mul)
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i19 = load i32, i32* %hashw, align 8
  %hashw75 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 2
  store i32 %i19, i32* %hashw75, align 8
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i20 = load i32*, i32** %hash, align 8
  %hash76 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 4
  store i32* %i20, i32** %hash76, align 8
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i21 = load i32, i32* %width, align 8
  %width77 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 0
  store i32 %i21, i32* %width77, align 8
  br label %for.cond78

for.cond78:                                       ; preds = %for.inc114, %if.end72
  %j.0 = phi i32 [ 0, %if.end72 ], [ %j.1, %for.inc114 ]
  %i.2 = phi i32 [ 0, %if.end72 ], [ %inc115, %for.inc114 ]
  %size79 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i22 = load i32, i32* %size79, align 4
  %cmp80 = icmp slt i32 %i.2, %i22
  br i1 %cmp80, label %for.body82, label %for.end116

for.body82:                                       ; preds = %for.cond78
  %node83 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i23 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node83, align 8
  %idxprom84 = sext i32 %i.2 to i64
  %arrayidx85 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i23, i64 %idxprom84
  %amplitude86 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx85, i32 0, i32 0
  %amplitude86.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude86, i32 0, i32 0
  %amplitude86.real = load float, float* %amplitude86.realp, align 8
  %amplitude86.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude86, i32 0, i32 1
  %amplitude86.imag = load float, float* %amplitude86.imagp, align 4
  %tobool87 = fcmp une float %amplitude86.real, 0.000000e+00
  %tobool88 = fcmp une float %amplitude86.imag, 0.000000e+00
  %tobool89 = or i1 %tobool87, %tobool88
  br i1 %tobool89, label %if.then90, label %if.end113

if.then90:                                        ; preds = %for.body82
  %node91 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i24 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node91, align 8
  %idxprom92 = sext i32 %i.2 to i64
  %arrayidx93 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i24, i64 %idxprom92
  %state94 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx93, i32 0, i32 1
  %i25 = load i64, i64* %state94, align 8
  %node95 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 3
  %i26 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node95, align 8
  %idxprom96 = sext i32 %j.0 to i64
  %arrayidx97 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i26, i64 %idxprom96
  %state98 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx97, i32 0, i32 1
  store i64 %i25, i64* %state98, align 8
  %node99 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i27 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node99, align 8
  %idxprom100 = sext i32 %i.2 to i64
  %arrayidx101 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i27, i64 %idxprom100
  %amplitude102 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx101, i32 0, i32 0
  %amplitude102.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude102, i32 0, i32 0
  %amplitude102.real = load float, float* %amplitude102.realp, align 8
  %amplitude102.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude102, i32 0, i32 1
  %amplitude102.imag = load float, float* %amplitude102.imagp, align 4
  %mul_ac = fmul float %amplitude102.real, 1.000000e+00
  %mul_bd = fmul float %amplitude102.imag, 0.000000e+00
  %mul_ad = fmul float %amplitude102.real, 0.000000e+00
  %mul_bc = fmul float %amplitude102.imag, 1.000000e+00
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then90
  %isnan_cmp103 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp103, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call104 = call <2 x float> @__mulsc3(float %amplitude102.real, float %amplitude102.imag, float 1.000000e+00, float 0.000000e+00) #9
  %i28 = bitcast { float, float }* %coerce105 to <2 x float>*
  store <2 x float> %call104, <2 x float>* %i28, align 4
  %coerce105.realp = getelementptr inbounds { float, float }, { float, float }* %coerce105, i32 0, i32 0
  %coerce105.real = load float, float* %coerce105.realp, align 4
  %coerce105.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce105, i32 0, i32 1
  %coerce105.imag = load float, float* %coerce105.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then90
  %real_mul_phi = phi float [ %mul_r, %if.then90 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce105.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then90 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce105.imag, %complex_mul_libcall ]
  %call106 = call double @sqrt(double %d.0) #9
  %conv107 = fptrunc double %call106 to float
  %i29 = fdiv float %real_mul_phi, %conv107
  %i30 = fdiv float %imag_mul_phi, %conv107
  %node108 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %out, i32 0, i32 3
  %i31 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node108, align 8
  %idxprom109 = sext i32 %j.0 to i64
  %arrayidx110 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i31, i64 %idxprom109
  %amplitude111 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx110, i32 0, i32 0
  %amplitude111.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude111, i32 0, i32 0
  %amplitude111.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude111, i32 0, i32 1
  store float %i29, float* %amplitude111.realp, align 8
  store float %i30, float* %amplitude111.imagp, align 4
  %inc112 = add nsw i32 %j.0, 1
  br label %if.end113

if.end113:                                        ; preds = %complex_mul_cont, %for.body82
  %j.1 = phi i32 [ %inc112, %complex_mul_cont ], [ %j.0, %for.body82 ]
  br label %for.inc114

for.inc114:                                       ; preds = %if.end113
  %inc115 = add nsw i32 %i.2, 1
  br label %for.cond78

for.end116:                                       ; preds = %for.cond78
  call void @quantum_delete_qureg_hashpreserve(%struct.quantum_reg_struct* %reg)
  %i32 = bitcast %struct.quantum_reg_struct* %reg to i8*
  %i33 = bitcast %struct.quantum_reg_struct* %out to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i32, i8* align 8 %i33, i64 32, i1 false)
  br label %return

return:                                           ; preds = %for.end116, %if.then
  %retval.0 = phi i32 [ 0, %if.then ], [ %result.0, %for.end116 ]
  ret i32 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @test_sum(i32 %compare, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %conv = sext i32 %compare to i64
  %sub = sub nsw i32 %width, 1
  %sh_prom = zext i32 %sub to i64
  %shl = shl i64 1, %sh_prom
  %and = and i64 %conv, %shl
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %mul = mul nsw i32 2, %width
  %sub1 = sub nsw i32 %mul, 1
  %sub2 = sub nsw i32 %width, 1
  call void @quantum_cnot(i32 %sub1, i32 %sub2, %struct.quantum_reg_struct* %reg)
  %mul3 = mul nsw i32 2, %width
  %sub4 = sub nsw i32 %mul3, 1
  call void @quantum_sigma_x(i32 %sub4, %struct.quantum_reg_struct* %reg)
  %mul5 = mul nsw i32 2, %width
  %sub6 = sub nsw i32 %mul5, 1
  call void @quantum_cnot(i32 %sub6, i32 0, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.else:                                          ; preds = %entry
  %mul7 = mul nsw i32 2, %width
  %sub8 = sub nsw i32 %mul7, 1
  call void @quantum_sigma_x(i32 %sub8, %struct.quantum_reg_struct* %reg)
  %mul9 = mul nsw i32 2, %width
  %sub10 = sub nsw i32 %mul9, 1
  %sub11 = sub nsw i32 %width, 1
  call void @quantum_cnot(i32 %sub10, i32 %sub11, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %sub12 = sub nsw i32 %width, 2
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ %sub12, %if.end ], [ %dec, %for.inc ]
  %cmp = icmp sgt i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %shl14 = shl i32 1, %i.0
  %and15 = and i32 %compare, %shl14
  %tobool16 = icmp ne i32 %and15, 0
  br i1 %tobool16, label %if.then17, label %if.else22

if.then17:                                        ; preds = %for.body
  %add = add nsw i32 %i.0, 1
  %add18 = add nsw i32 %width, %i.0
  call void @quantum_toffoli(i32 %add, i32 %add18, i32 %i.0, %struct.quantum_reg_struct* %reg)
  %add19 = add nsw i32 %width, %i.0
  call void @quantum_sigma_x(i32 %add19, %struct.quantum_reg_struct* %reg)
  %add20 = add nsw i32 %i.0, 1
  %add21 = add nsw i32 %width, %i.0
  call void @quantum_toffoli(i32 %add20, i32 %add21, i32 0, %struct.quantum_reg_struct* %reg)
  br label %if.end26

if.else22:                                        ; preds = %for.body
  %add23 = add nsw i32 %width, %i.0
  call void @quantum_sigma_x(i32 %add23, %struct.quantum_reg_struct* %reg)
  %add24 = add nsw i32 %i.0, 1
  %add25 = add nsw i32 %width, %i.0
  call void @quantum_toffoli(i32 %add24, i32 %add25, i32 %i.0, %struct.quantum_reg_struct* %reg)
  br label %if.end26

if.end26:                                         ; preds = %if.else22, %if.then17
  br label %for.inc

for.inc:                                          ; preds = %if.end26
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %and27 = and i32 %compare, 1
  %tobool28 = icmp ne i32 %and27, 0
  br i1 %tobool28, label %if.then29, label %if.end30

if.then29:                                        ; preds = %for.end
  call void @quantum_sigma_x(i32 %width, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %width, i32 1, i32 0, %struct.quantum_reg_struct* %reg)
  br label %if.end30

if.end30:                                         ; preds = %if.then29, %for.end
  %mul31 = mul nsw i32 2, %width
  %add32 = add nsw i32 %mul31, 1
  %mul33 = mul nsw i32 2, %width
  call void @quantum_toffoli(i32 %add32, i32 0, i32 %mul33, %struct.quantum_reg_struct* %reg)
  %and34 = and i32 %compare, 1
  %tobool35 = icmp ne i32 %and34, 0
  br i1 %tobool35, label %if.then36, label %if.end37

if.then36:                                        ; preds = %if.end30
  call void @quantum_toffoli(i32 %width, i32 1, i32 0, %struct.quantum_reg_struct* %reg)
  call void @quantum_sigma_x(i32 %width, %struct.quantum_reg_struct* %reg)
  br label %if.end37

if.end37:                                         ; preds = %if.then36, %if.end30
  br label %for.cond38

for.cond38:                                       ; preds = %for.inc57, %if.end37
  %i.1 = phi i32 [ 1, %if.end37 ], [ %inc, %for.inc57 ]
  %sub39 = sub nsw i32 %width, 2
  %cmp40 = icmp sle i32 %i.1, %sub39
  br i1 %cmp40, label %for.body42, label %for.end58

for.body42:                                       ; preds = %for.cond38
  %shl43 = shl i32 1, %i.1
  %and44 = and i32 %compare, %shl43
  %tobool45 = icmp ne i32 %and44, 0
  br i1 %tobool45, label %if.then46, label %if.else52

if.then46:                                        ; preds = %for.body42
  %add47 = add nsw i32 %i.1, 1
  %add48 = add nsw i32 %width, %i.1
  call void @quantum_toffoli(i32 %add47, i32 %add48, i32 0, %struct.quantum_reg_struct* %reg)
  %add49 = add nsw i32 %width, %i.1
  call void @quantum_sigma_x(i32 %add49, %struct.quantum_reg_struct* %reg)
  %add50 = add nsw i32 %i.1, 1
  %add51 = add nsw i32 %width, %i.1
  call void @quantum_toffoli(i32 %add50, i32 %add51, i32 %i.1, %struct.quantum_reg_struct* %reg)
  br label %if.end56

if.else52:                                        ; preds = %for.body42
  %add53 = add nsw i32 %i.1, 1
  %add54 = add nsw i32 %width, %i.1
  call void @quantum_toffoli(i32 %add53, i32 %add54, i32 %i.1, %struct.quantum_reg_struct* %reg)
  %add55 = add nsw i32 %width, %i.1
  call void @quantum_sigma_x(i32 %add55, %struct.quantum_reg_struct* %reg)
  br label %if.end56

if.end56:                                         ; preds = %if.else52, %if.then46
  br label %for.inc57

for.inc57:                                        ; preds = %if.end56
  %inc = add nsw i32 %i.1, 1
  br label %for.cond38

for.end58:                                        ; preds = %for.cond38
  %sub59 = sub nsw i32 %width, 1
  %shl60 = shl i32 1, %sub59
  %and61 = and i32 %compare, %shl60
  %tobool62 = icmp ne i32 %and61, 0
  br i1 %tobool62, label %if.then63, label %if.else71

if.then63:                                        ; preds = %for.end58
  %mul64 = mul nsw i32 2, %width
  %sub65 = sub nsw i32 %mul64, 1
  call void @quantum_cnot(i32 %sub65, i32 0, %struct.quantum_reg_struct* %reg)
  %mul66 = mul nsw i32 2, %width
  %sub67 = sub nsw i32 %mul66, 1
  call void @quantum_sigma_x(i32 %sub67, %struct.quantum_reg_struct* %reg)
  %mul68 = mul nsw i32 2, %width
  %sub69 = sub nsw i32 %mul68, 1
  %sub70 = sub nsw i32 %width, 1
  call void @quantum_cnot(i32 %sub69, i32 %sub70, %struct.quantum_reg_struct* %reg)
  br label %if.end77

if.else71:                                        ; preds = %for.end58
  %mul72 = mul nsw i32 2, %width
  %sub73 = sub nsw i32 %mul72, 1
  %sub74 = sub nsw i32 %width, 1
  call void @quantum_cnot(i32 %sub73, i32 %sub74, %struct.quantum_reg_struct* %reg)
  %mul75 = mul nsw i32 2, %width
  %sub76 = sub nsw i32 %mul75, 1
  call void @quantum_sigma_x(i32 %sub76, %struct.quantum_reg_struct* %reg)
  br label %if.end77

if.end77:                                         ; preds = %if.else71, %if.then63
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @muxfa(i32 %a, i32 %b_in, i32 %c_in, i32 %c_out, i32 %xlt_l, i32 %L, i32 %total, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %cmp1 = icmp eq i32 %a, 3
  br i1 %cmp1, label %if.then2, label %if.end3

if.then2:                                         ; preds = %if.end
  call void @quantum_toffoli(i32 %L, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %L, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end3

if.end3:                                          ; preds = %if.then2, %if.end
  %cmp4 = icmp eq i32 %a, 1
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end3
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end6

if.end6:                                          ; preds = %if.then5, %if.end3
  %cmp7 = icmp eq i32 %a, 2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end6
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  br label %if.end9

if.end9:                                          ; preds = %if.then8, %if.end6
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @muxfa_inv(i32 %a, i32 %b_in, i32 %c_in, i32 %c_out, i32 %xlt_l, i32 %L, i32 %total, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %cmp1 = icmp eq i32 %a, 3
  br i1 %cmp1, label %if.then2, label %if.end3

if.then2:                                         ; preds = %if.end
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %L, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  br label %if.end3

if.end3:                                          ; preds = %if.then2, %if.end
  %cmp4 = icmp eq i32 %a, 1
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end3
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  br label %if.end6

if.end6:                                          ; preds = %if.then5, %if.end3
  %cmp7 = icmp eq i32 %a, 2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end6
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %b_in, i32 %c_in, i32 %c_out, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %b_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  br label %if.end9

if.end9:                                          ; preds = %if.then8, %if.end6
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @muxha(i32 %a, i32 %b_in, i32 %c_in, i32 %xlt_l, i32 %L, i32 %total, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %cmp1 = icmp eq i32 %a, 3
  br i1 %cmp1, label %if.then2, label %if.end3

if.then2:                                         ; preds = %if.end
  call void @quantum_cnot(i32 %L, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end3

if.end3:                                          ; preds = %if.then2, %if.end
  %cmp4 = icmp eq i32 %a, 1
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end3
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end6

if.end6:                                          ; preds = %if.then5, %if.end3
  %cmp7 = icmp eq i32 %a, 2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end6
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  br label %if.end9

if.end9:                                          ; preds = %if.then8, %if.end6
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @muxha_inv(i32 %a, i32 %b_in, i32 %c_in, i32 %xlt_l, i32 %L, i32 %total, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %cmp = icmp eq i32 %a, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %cmp1 = icmp eq i32 %a, 3
  br i1 %cmp1, label %if.then2, label %if.end3

if.then2:                                         ; preds = %if.end
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %L, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end3

if.end3:                                          ; preds = %if.then2, %if.end
  %cmp4 = icmp eq i32 %a, 1
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end3
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  br label %if.end6

if.end6:                                          ; preds = %if.then5, %if.end3
  %cmp7 = icmp eq i32 %a, 2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end6
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  call void @quantum_cnot(i32 %b_in, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_toffoli(i32 %L, i32 %xlt_l, i32 %c_in, %struct.quantum_reg_struct* %reg)
  call void @quantum_sigma_x(i32 %xlt_l, %struct.quantum_reg_struct* %reg)
  br label %if.end9

if.end9:                                          ; preds = %if.then8, %if.end6
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @madd(i32 %a, i32 %a_inv, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %mul = mul nsw i32 4, %width
  %add = add nsw i32 %mul, 2
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %sub = sub nsw i32 %width, 1
  %cmp = icmp slt i32 %i.0, %sub
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %shl = shl i32 1, %i.0
  %and = and i32 %shl, %a
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %for.body
  br label %if.end

if.else:                                          ; preds = %for.body
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %j.0 = phi i32 [ 2, %if.then ], [ 0, %if.else ]
  %shl1 = shl i32 1, %i.0
  %and2 = and i32 %shl1, %a_inv
  %tobool3 = icmp ne i32 %and2, 0
  br i1 %tobool3, label %if.then4, label %if.end6

if.then4:                                         ; preds = %if.end
  %add5 = add nsw i32 %j.0, 1
  br label %if.end6

if.end6:                                          ; preds = %if.then4, %if.end
  %j.1 = phi i32 [ %add5, %if.then4 ], [ %j.0, %if.end ]
  %add7 = add nsw i32 %width, %i.0
  %add8 = add nsw i32 %i.0, 1
  %mul9 = mul nsw i32 2, %width
  %mul10 = mul nsw i32 2, %width
  %add11 = add nsw i32 %mul10, 1
  call void @muxfa(i32 %j.1, i32 %add7, i32 %i.0, i32 %add8, i32 %mul9, i32 %add11, i32 %add, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %if.end6
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %sub12 = sub nsw i32 %width, 1
  %shl13 = shl i32 1, %sub12
  %and14 = and i32 %shl13, %a
  %tobool15 = icmp ne i32 %and14, 0
  br i1 %tobool15, label %if.then16, label %if.end17

if.then16:                                        ; preds = %for.end
  br label %if.end17

if.end17:                                         ; preds = %if.then16, %for.end
  %j.2 = phi i32 [ 2, %if.then16 ], [ 0, %for.end ]
  %sub18 = sub nsw i32 %width, 1
  %shl19 = shl i32 1, %sub18
  %and20 = and i32 %shl19, %a_inv
  %tobool21 = icmp ne i32 %and20, 0
  br i1 %tobool21, label %if.then22, label %if.end24

if.then22:                                        ; preds = %if.end17
  %add23 = add nsw i32 %j.2, 1
  br label %if.end24

if.end24:                                         ; preds = %if.then22, %if.end17
  %j.3 = phi i32 [ %add23, %if.then22 ], [ %j.2, %if.end17 ]
  %mul25 = mul nsw i32 2, %width
  %sub26 = sub nsw i32 %mul25, 1
  %sub27 = sub nsw i32 %width, 1
  %mul28 = mul nsw i32 2, %width
  %mul29 = mul nsw i32 2, %width
  %add30 = add nsw i32 %mul29, 1
  call void @muxha(i32 %j.3, i32 %sub26, i32 %sub27, i32 %mul28, i32 %add30, i32 %add, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @madd_inv(i32 %a, i32 %a_inv, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %mul = mul nsw i32 4, %width
  %add = add nsw i32 %mul, 2
  %sub = sub nsw i32 %width, 1
  %shl = shl i32 1, %sub
  %and = and i32 %shl, %a
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %j.0 = phi i32 [ 2, %if.then ], [ 0, %entry ]
  %sub1 = sub nsw i32 %width, 1
  %shl2 = shl i32 1, %sub1
  %and3 = and i32 %shl2, %a_inv
  %tobool4 = icmp ne i32 %and3, 0
  br i1 %tobool4, label %if.then5, label %if.end7

if.then5:                                         ; preds = %if.end
  %add6 = add nsw i32 %j.0, 1
  br label %if.end7

if.end7:                                          ; preds = %if.then5, %if.end
  %j.1 = phi i32 [ %add6, %if.then5 ], [ %j.0, %if.end ]
  %sub8 = sub nsw i32 %width, 1
  %mul9 = mul nsw i32 2, %width
  %sub10 = sub nsw i32 %mul9, 1
  %mul11 = mul nsw i32 2, %width
  %mul12 = mul nsw i32 2, %width
  %add13 = add nsw i32 %mul12, 1
  call void @muxha_inv(i32 %j.1, i32 %sub8, i32 %sub10, i32 %mul11, i32 %add13, i32 %add, %struct.quantum_reg_struct* %reg)
  %sub14 = sub nsw i32 %width, 2
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end7
  %i.0 = phi i32 [ %sub14, %if.end7 ], [ %dec, %for.inc ]
  %cmp = icmp sge i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %shl15 = shl i32 1, %i.0
  %and16 = and i32 %shl15, %a
  %tobool17 = icmp ne i32 %and16, 0
  br i1 %tobool17, label %if.then18, label %if.else

if.then18:                                        ; preds = %for.body
  br label %if.end19

if.else:                                          ; preds = %for.body
  br label %if.end19

if.end19:                                         ; preds = %if.else, %if.then18
  %j.2 = phi i32 [ 2, %if.then18 ], [ 0, %if.else ]
  %shl20 = shl i32 1, %i.0
  %and21 = and i32 %shl20, %a_inv
  %tobool22 = icmp ne i32 %and21, 0
  br i1 %tobool22, label %if.then23, label %if.end25

if.then23:                                        ; preds = %if.end19
  %add24 = add nsw i32 %j.2, 1
  br label %if.end25

if.end25:                                         ; preds = %if.then23, %if.end19
  %j.3 = phi i32 [ %add24, %if.then23 ], [ %j.2, %if.end19 ]
  %add26 = add nsw i32 %width, %i.0
  %add27 = add nsw i32 %width, 1
  %add28 = add nsw i32 %add27, %i.0
  %mul29 = mul nsw i32 2, %width
  %mul30 = mul nsw i32 2, %width
  %add31 = add nsw i32 %mul30, 1
  call void @muxfa_inv(i32 %j.3, i32 %i.0, i32 %add26, i32 %add28, i32 %mul29, i32 %add31, i32 %add, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %if.end25
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @addn(i32 %N, i32 %a, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %sub = sub nsw i32 %N, %a
  call void @test_sum(i32 %sub, i32 %width, %struct.quantum_reg_struct* %reg)
  %shl = shl i32 1, %width
  %add = add nsw i32 %shl, %a
  %sub1 = sub nsw i32 %add, %N
  call void @madd(i32 %sub1, i32 %a, i32 %width, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @addn_inv(i32 %N, i32 %a, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %mul = mul nsw i32 2, %width
  %add = add nsw i32 %mul, 1
  %mul1 = mul nsw i32 2, %width
  call void @quantum_cnot(i32 %add, i32 %mul1, %struct.quantum_reg_struct* %reg)
  %shl = shl i32 1, %width
  %sub = sub nsw i32 %shl, %a
  %sub2 = sub nsw i32 %N, %a
  call void @madd_inv(i32 %sub, i32 %sub2, i32 %width, %struct.quantum_reg_struct* %reg)
  call void @quantum_swaptheleads(i32 %width, %struct.quantum_reg_struct* %reg)
  call void @test_sum(i32 %a, i32 %width, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @add_mod_n(i32 %N, i32 %a, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  call void @addn(i32 %N, i32 %a, i32 %width, %struct.quantum_reg_struct* %reg)
  call void @addn_inv(i32 %N, i32 %a, i32 %width, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_mu2char(i64 %mu, i8* %buf) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %mu.addr.0 = phi i64 [ %mu, %entry ], [ %rem, %for.inc ]
  %cmp = icmp slt i32 %i.0, 8
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %sub = sub nsw i32 8, %i.0
  %sub1 = sub nsw i32 %sub, 1
  %mul = mul nsw i32 %sub1, 8
  %sh_prom = zext i32 %mul to i64
  %shl = shl i64 1, %sh_prom
  %div = udiv i64 %mu.addr.0, %shl
  %conv = trunc i64 %div to i8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i8, i8* %buf, i64 %idxprom
  store i8 %conv, i8* %arrayidx, align 1
  %sub2 = sub nsw i32 8, %i.0
  %sub3 = sub nsw i32 %sub2, 1
  %mul4 = mul nsw i32 %sub3, 8
  %sh_prom5 = zext i32 %mul4 to i64
  %shl6 = shl i64 1, %sh_prom5
  %rem = urem i64 %mu.addr.0, %shl6
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_int2char(i32 %j, i8* %buf) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %j.addr.0 = phi i32 [ %j, %entry ], [ %rem, %for.inc ]
  %cmp = icmp slt i32 %i.0, 4
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %sub = sub nsw i32 4, %i.0
  %sub1 = sub nsw i32 %sub, 1
  %mul = mul nsw i32 %sub1, 8
  %shl = shl i32 1, %mul
  %div = sdiv i32 %j.addr.0, %shl
  %conv = trunc i32 %div to i8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i8, i8* %buf, i64 %idxprom
  store i8 %conv, i8* %arrayidx, align 1
  %sub2 = sub nsw i32 4, %i.0
  %sub3 = sub nsw i32 %sub2, 1
  %mul4 = mul nsw i32 %sub3, 8
  %shl5 = shl i32 1, %mul4
  %rem = srem i32 %j.addr.0, %shl5
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_double2char(double %d, i8* %buf) #0 {
entry:
  %d.addr = alloca double, align 8
  store double %d, double* %d.addr, align 8
  %i = bitcast double* %d.addr to i8*
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %conv = sext i32 %i.0 to i64
  %cmp = icmp ult i64 %conv, 8
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i8, i8* %i, i64 %idxprom
  %i1 = load i8, i8* %arrayidx, align 1
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds i8, i8* %buf, i64 %idxprom2
  store i8 %i1, i8* %arrayidx3, align 1
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @quantum_char2mu(i8* %buf) #0 {
entry:
  %sub = sub nsw i32 8, 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ %sub, %entry ], [ %dec, %for.inc ]
  %mu.0 = phi i64 [ 0, %entry ], [ %add, %for.inc ]
  %cmp = icmp sge i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i8, i8* %buf, i64 %idxprom
  %i = load i8, i8* %arrayidx, align 1
  %conv = zext i8 %i to i64
  %sub1 = sub nsw i32 8, %i.0
  %sub2 = sub nsw i32 %sub1, 1
  %mul = mul nsw i32 8, %sub2
  %sh_prom = zext i32 %mul to i64
  %shl = shl i64 1, %sh_prom
  %mul3 = mul i64 %conv, %shl
  %add = add i64 %mu.0, %mul3
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i64 %mu.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_char2int(i8* %buf) #0 {
entry:
  %sub = sub nsw i32 4, 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ %sub, %entry ], [ %dec, %for.inc ]
  %j.0 = phi i32 [ 0, %entry ], [ %add, %for.inc ]
  %cmp = icmp sge i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i8, i8* %buf, i64 %idxprom
  %i = load i8, i8* %arrayidx, align 1
  %conv = zext i8 %i to i32
  %sub1 = sub nsw i32 4, %i.0
  %sub2 = sub nsw i32 %sub1, 1
  %mul = mul nsw i32 8, %sub2
  %shl = shl i32 1, %mul
  %mul3 = mul nsw i32 %conv, %shl
  %add = add nsw i32 %j.0, %mul3
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i32 %j.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local double @quantum_char2double(i8* %buf) #0 {
entry:
  %i = bitcast i8* %buf to double*
  %i1 = load double, double* %i, align 8
  ret double %i1
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_objcode_start() #0 {
entry:
  store i32 1, i32* @opstatus, align 4
  store i64 1, i64* @allocated, align 8
  %call = call noalias i8* @malloc(i64 65536) #9
  store i8* %call, i8** @objcode, align 8
  %i = load i8*, i8** @objcode, align 8
  %tobool = icmp ne i8* %i, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %call1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.27, i64 0, i64 0))
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %entry
  %call2 = call i64 @quantum_memman(i64 65536)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_objcode_stop() #0 {
entry:
  store i32 0, i32* @opstatus, align 4
  %i = load i8*, i8** @objcode, align 8
  call void @free(i8* %i) #9
  store i8* null, i8** @objcode, align 8
  %i1 = load i64, i64* @allocated, align 8
  %sub = sub i64 0, %i1
  %mul = mul i64 %sub, 65536
  %mul1 = mul i64 %mul, 1
  %call = call i64 @quantum_memman(i64 %mul1)
  store i64 0, i64* @allocated, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_objcode_put(i8 zeroext %operation, ...) #0 {
entry:
  %args = alloca [1 x %struct.__va_list_tag], align 16
  %buf = alloca [80 x i8], align 16
  %i = load i32, i32* @opstatus, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %arraydecay = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %arraydecay1 = bitcast %struct.__va_list_tag* %arraydecay to i8*
  call void @llvm.va_start(i8* %arraydecay1)
  %arrayidx = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  store i8 %operation, i8* %arrayidx, align 16
  %conv = zext i8 %operation to i32
  switch i32 %conv, label %sw.default [
    i32 0, label %sw.bb
    i32 1, label %sw.bb4
    i32 12, label %sw.bb4
    i32 2, label %sw.bb31
    i32 3, label %sw.bb71
    i32 4, label %sw.bb71
    i32 5, label %sw.bb71
    i32 6, label %sw.bb71
    i32 129, label %sw.bb71
    i32 130, label %sw.bb71
    i32 14, label %sw.bb71
    i32 7, label %sw.bb85
    i32 8, label %sw.bb85
    i32 9, label %sw.bb85
    i32 10, label %sw.bb85
    i32 11, label %sw.bb85
    i32 13, label %sw.bb109
    i32 128, label %sw.bb149
    i32 255, label %sw.bb149
  ]

sw.bb:                                            ; preds = %if.end
  %arraydecay2 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay2, i32 0, i32 0
  %gp_offset = load i32, i32* %gp_offset_p, align 16
  %fits_in_gp = icmp ule i32 %gp_offset, 40
  br i1 %fits_in_gp, label %vaarg.in_reg, label %vaarg.in_mem

vaarg.in_reg:                                     ; preds = %sw.bb
  %i1 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay2, i32 0, i32 3
  %reg_save_area = load i8*, i8** %i1, align 16
  %i2 = getelementptr i8, i8* %reg_save_area, i32 %gp_offset
  %i3 = bitcast i8* %i2 to i64*
  %i4 = add i32 %gp_offset, 8
  store i32 %i4, i32* %gp_offset_p, align 16
  br label %vaarg.end

vaarg.in_mem:                                     ; preds = %sw.bb
  %overflow_arg_area_p = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay2, i32 0, i32 2
  %overflow_arg_area = load i8*, i8** %overflow_arg_area_p, align 8
  %i5 = bitcast i8* %overflow_arg_area to i64*
  %overflow_arg_area.next = getelementptr i8, i8* %overflow_arg_area, i32 8
  store i8* %overflow_arg_area.next, i8** %overflow_arg_area_p, align 8
  br label %vaarg.end

vaarg.end:                                        ; preds = %vaarg.in_mem, %vaarg.in_reg
  %vaarg.addr = phi i64* [ %i3, %vaarg.in_reg ], [ %i5, %vaarg.in_mem ]
  %i6 = load i64, i64* %vaarg.addr, align 8
  %arrayidx3 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 1
  call void @quantum_mu2char(i64 %i6, i8* %arrayidx3)
  br label %sw.epilog

sw.bb4:                                           ; preds = %if.end, %if.end
  %arraydecay5 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p6 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay5, i32 0, i32 0
  %gp_offset7 = load i32, i32* %gp_offset_p6, align 16
  %fits_in_gp8 = icmp ule i32 %gp_offset7, 40
  br i1 %fits_in_gp8, label %vaarg.in_reg9, label %vaarg.in_mem11

vaarg.in_reg9:                                    ; preds = %sw.bb4
  %i7 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay5, i32 0, i32 3
  %reg_save_area10 = load i8*, i8** %i7, align 16
  %i8 = getelementptr i8, i8* %reg_save_area10, i32 %gp_offset7
  %i9 = bitcast i8* %i8 to i32*
  %i10 = add i32 %gp_offset7, 8
  store i32 %i10, i32* %gp_offset_p6, align 16
  br label %vaarg.end15

vaarg.in_mem11:                                   ; preds = %sw.bb4
  %overflow_arg_area_p12 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay5, i32 0, i32 2
  %overflow_arg_area13 = load i8*, i8** %overflow_arg_area_p12, align 8
  %i11 = bitcast i8* %overflow_arg_area13 to i32*
  %overflow_arg_area.next14 = getelementptr i8, i8* %overflow_arg_area13, i32 8
  store i8* %overflow_arg_area.next14, i8** %overflow_arg_area_p12, align 8
  br label %vaarg.end15

vaarg.end15:                                      ; preds = %vaarg.in_mem11, %vaarg.in_reg9
  %vaarg.addr16 = phi i32* [ %i9, %vaarg.in_reg9 ], [ %i11, %vaarg.in_mem11 ]
  %i12 = load i32, i32* %vaarg.addr16, align 4
  %arrayidx17 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 1
  call void @quantum_int2char(i32 %i12, i8* %arrayidx17)
  %arraydecay18 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p19 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay18, i32 0, i32 0
  %gp_offset20 = load i32, i32* %gp_offset_p19, align 16
  %fits_in_gp21 = icmp ule i32 %gp_offset20, 40
  br i1 %fits_in_gp21, label %vaarg.in_reg22, label %vaarg.in_mem24

vaarg.in_reg22:                                   ; preds = %vaarg.end15
  %i13 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay18, i32 0, i32 3
  %reg_save_area23 = load i8*, i8** %i13, align 16
  %i14 = getelementptr i8, i8* %reg_save_area23, i32 %gp_offset20
  %i15 = bitcast i8* %i14 to i32*
  %i16 = add i32 %gp_offset20, 8
  store i32 %i16, i32* %gp_offset_p19, align 16
  br label %vaarg.end28

vaarg.in_mem24:                                   ; preds = %vaarg.end15
  %overflow_arg_area_p25 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay18, i32 0, i32 2
  %overflow_arg_area26 = load i8*, i8** %overflow_arg_area_p25, align 8
  %i17 = bitcast i8* %overflow_arg_area26 to i32*
  %overflow_arg_area.next27 = getelementptr i8, i8* %overflow_arg_area26, i32 8
  store i8* %overflow_arg_area.next27, i8** %overflow_arg_area_p25, align 8
  br label %vaarg.end28

vaarg.end28:                                      ; preds = %vaarg.in_mem24, %vaarg.in_reg22
  %vaarg.addr29 = phi i32* [ %i15, %vaarg.in_reg22 ], [ %i17, %vaarg.in_mem24 ]
  %i18 = load i32, i32* %vaarg.addr29, align 4
  %arrayidx30 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 5
  call void @quantum_int2char(i32 %i18, i8* %arrayidx30)
  br label %sw.epilog

sw.bb31:                                          ; preds = %if.end
  %arraydecay32 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p33 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay32, i32 0, i32 0
  %gp_offset34 = load i32, i32* %gp_offset_p33, align 16
  %fits_in_gp35 = icmp ule i32 %gp_offset34, 40
  br i1 %fits_in_gp35, label %vaarg.in_reg36, label %vaarg.in_mem38

vaarg.in_reg36:                                   ; preds = %sw.bb31
  %i19 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay32, i32 0, i32 3
  %reg_save_area37 = load i8*, i8** %i19, align 16
  %i20 = getelementptr i8, i8* %reg_save_area37, i32 %gp_offset34
  %i21 = bitcast i8* %i20 to i32*
  %i22 = add i32 %gp_offset34, 8
  store i32 %i22, i32* %gp_offset_p33, align 16
  br label %vaarg.end42

vaarg.in_mem38:                                   ; preds = %sw.bb31
  %overflow_arg_area_p39 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay32, i32 0, i32 2
  %overflow_arg_area40 = load i8*, i8** %overflow_arg_area_p39, align 8
  %i23 = bitcast i8* %overflow_arg_area40 to i32*
  %overflow_arg_area.next41 = getelementptr i8, i8* %overflow_arg_area40, i32 8
  store i8* %overflow_arg_area.next41, i8** %overflow_arg_area_p39, align 8
  br label %vaarg.end42

vaarg.end42:                                      ; preds = %vaarg.in_mem38, %vaarg.in_reg36
  %vaarg.addr43 = phi i32* [ %i21, %vaarg.in_reg36 ], [ %i23, %vaarg.in_mem38 ]
  %i24 = load i32, i32* %vaarg.addr43, align 4
  %arrayidx44 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 1
  call void @quantum_int2char(i32 %i24, i8* %arrayidx44)
  %arraydecay45 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p46 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay45, i32 0, i32 0
  %gp_offset47 = load i32, i32* %gp_offset_p46, align 16
  %fits_in_gp48 = icmp ule i32 %gp_offset47, 40
  br i1 %fits_in_gp48, label %vaarg.in_reg49, label %vaarg.in_mem51

vaarg.in_reg49:                                   ; preds = %vaarg.end42
  %i25 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay45, i32 0, i32 3
  %reg_save_area50 = load i8*, i8** %i25, align 16
  %i26 = getelementptr i8, i8* %reg_save_area50, i32 %gp_offset47
  %i27 = bitcast i8* %i26 to i32*
  %i28 = add i32 %gp_offset47, 8
  store i32 %i28, i32* %gp_offset_p46, align 16
  br label %vaarg.end55

vaarg.in_mem51:                                   ; preds = %vaarg.end42
  %overflow_arg_area_p52 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay45, i32 0, i32 2
  %overflow_arg_area53 = load i8*, i8** %overflow_arg_area_p52, align 8
  %i29 = bitcast i8* %overflow_arg_area53 to i32*
  %overflow_arg_area.next54 = getelementptr i8, i8* %overflow_arg_area53, i32 8
  store i8* %overflow_arg_area.next54, i8** %overflow_arg_area_p52, align 8
  br label %vaarg.end55

vaarg.end55:                                      ; preds = %vaarg.in_mem51, %vaarg.in_reg49
  %vaarg.addr56 = phi i32* [ %i27, %vaarg.in_reg49 ], [ %i29, %vaarg.in_mem51 ]
  %i30 = load i32, i32* %vaarg.addr56, align 4
  %arrayidx57 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 5
  call void @quantum_int2char(i32 %i30, i8* %arrayidx57)
  %arraydecay58 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p59 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay58, i32 0, i32 0
  %gp_offset60 = load i32, i32* %gp_offset_p59, align 16
  %fits_in_gp61 = icmp ule i32 %gp_offset60, 40
  br i1 %fits_in_gp61, label %vaarg.in_reg62, label %vaarg.in_mem64

vaarg.in_reg62:                                   ; preds = %vaarg.end55
  %i31 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay58, i32 0, i32 3
  %reg_save_area63 = load i8*, i8** %i31, align 16
  %i32 = getelementptr i8, i8* %reg_save_area63, i32 %gp_offset60
  %i33 = bitcast i8* %i32 to i32*
  %i34 = add i32 %gp_offset60, 8
  store i32 %i34, i32* %gp_offset_p59, align 16
  br label %vaarg.end68

vaarg.in_mem64:                                   ; preds = %vaarg.end55
  %overflow_arg_area_p65 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay58, i32 0, i32 2
  %overflow_arg_area66 = load i8*, i8** %overflow_arg_area_p65, align 8
  %i35 = bitcast i8* %overflow_arg_area66 to i32*
  %overflow_arg_area.next67 = getelementptr i8, i8* %overflow_arg_area66, i32 8
  store i8* %overflow_arg_area.next67, i8** %overflow_arg_area_p65, align 8
  br label %vaarg.end68

vaarg.end68:                                      ; preds = %vaarg.in_mem64, %vaarg.in_reg62
  %vaarg.addr69 = phi i32* [ %i33, %vaarg.in_reg62 ], [ %i35, %vaarg.in_mem64 ]
  %i36 = load i32, i32* %vaarg.addr69, align 4
  %arrayidx70 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 9
  call void @quantum_int2char(i32 %i36, i8* %arrayidx70)
  br label %sw.epilog

sw.bb71:                                          ; preds = %if.end, %if.end, %if.end, %if.end, %if.end, %if.end, %if.end
  %arraydecay72 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p73 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay72, i32 0, i32 0
  %gp_offset74 = load i32, i32* %gp_offset_p73, align 16
  %fits_in_gp75 = icmp ule i32 %gp_offset74, 40
  br i1 %fits_in_gp75, label %vaarg.in_reg76, label %vaarg.in_mem78

vaarg.in_reg76:                                   ; preds = %sw.bb71
  %i37 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay72, i32 0, i32 3
  %reg_save_area77 = load i8*, i8** %i37, align 16
  %i38 = getelementptr i8, i8* %reg_save_area77, i32 %gp_offset74
  %i39 = bitcast i8* %i38 to i32*
  %i40 = add i32 %gp_offset74, 8
  store i32 %i40, i32* %gp_offset_p73, align 16
  br label %vaarg.end82

vaarg.in_mem78:                                   ; preds = %sw.bb71
  %overflow_arg_area_p79 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay72, i32 0, i32 2
  %overflow_arg_area80 = load i8*, i8** %overflow_arg_area_p79, align 8
  %i41 = bitcast i8* %overflow_arg_area80 to i32*
  %overflow_arg_area.next81 = getelementptr i8, i8* %overflow_arg_area80, i32 8
  store i8* %overflow_arg_area.next81, i8** %overflow_arg_area_p79, align 8
  br label %vaarg.end82

vaarg.end82:                                      ; preds = %vaarg.in_mem78, %vaarg.in_reg76
  %vaarg.addr83 = phi i32* [ %i39, %vaarg.in_reg76 ], [ %i41, %vaarg.in_mem78 ]
  %i42 = load i32, i32* %vaarg.addr83, align 4
  %arrayidx84 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 1
  call void @quantum_int2char(i32 %i42, i8* %arrayidx84)
  br label %sw.epilog

sw.bb85:                                          ; preds = %if.end, %if.end, %if.end, %if.end, %if.end
  %arraydecay86 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p87 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay86, i32 0, i32 0
  %gp_offset88 = load i32, i32* %gp_offset_p87, align 16
  %fits_in_gp89 = icmp ule i32 %gp_offset88, 40
  br i1 %fits_in_gp89, label %vaarg.in_reg90, label %vaarg.in_mem92

vaarg.in_reg90:                                   ; preds = %sw.bb85
  %i43 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay86, i32 0, i32 3
  %reg_save_area91 = load i8*, i8** %i43, align 16
  %i44 = getelementptr i8, i8* %reg_save_area91, i32 %gp_offset88
  %i45 = bitcast i8* %i44 to i32*
  %i46 = add i32 %gp_offset88, 8
  store i32 %i46, i32* %gp_offset_p87, align 16
  br label %vaarg.end96

vaarg.in_mem92:                                   ; preds = %sw.bb85
  %overflow_arg_area_p93 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay86, i32 0, i32 2
  %overflow_arg_area94 = load i8*, i8** %overflow_arg_area_p93, align 8
  %i47 = bitcast i8* %overflow_arg_area94 to i32*
  %overflow_arg_area.next95 = getelementptr i8, i8* %overflow_arg_area94, i32 8
  store i8* %overflow_arg_area.next95, i8** %overflow_arg_area_p93, align 8
  br label %vaarg.end96

vaarg.end96:                                      ; preds = %vaarg.in_mem92, %vaarg.in_reg90
  %vaarg.addr97 = phi i32* [ %i45, %vaarg.in_reg90 ], [ %i47, %vaarg.in_mem92 ]
  %i48 = load i32, i32* %vaarg.addr97, align 4
  %arraydecay98 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %fp_offset_p = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay98, i32 0, i32 1
  %fp_offset = load i32, i32* %fp_offset_p, align 4
  %fits_in_fp = icmp ule i32 %fp_offset, 160
  br i1 %fits_in_fp, label %vaarg.in_reg99, label %vaarg.in_mem101

vaarg.in_reg99:                                   ; preds = %vaarg.end96
  %i49 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay98, i32 0, i32 3
  %reg_save_area100 = load i8*, i8** %i49, align 16
  %i50 = getelementptr i8, i8* %reg_save_area100, i32 %fp_offset
  %i51 = bitcast i8* %i50 to double*
  %i52 = add i32 %fp_offset, 16
  store i32 %i52, i32* %fp_offset_p, align 4
  br label %vaarg.end105

vaarg.in_mem101:                                  ; preds = %vaarg.end96
  %overflow_arg_area_p102 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay98, i32 0, i32 2
  %overflow_arg_area103 = load i8*, i8** %overflow_arg_area_p102, align 8
  %i53 = bitcast i8* %overflow_arg_area103 to double*
  %overflow_arg_area.next104 = getelementptr i8, i8* %overflow_arg_area103, i32 8
  store i8* %overflow_arg_area.next104, i8** %overflow_arg_area_p102, align 8
  br label %vaarg.end105

vaarg.end105:                                     ; preds = %vaarg.in_mem101, %vaarg.in_reg99
  %vaarg.addr106 = phi double* [ %i51, %vaarg.in_reg99 ], [ %i53, %vaarg.in_mem101 ]
  %i54 = load double, double* %vaarg.addr106, align 8
  %arrayidx107 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 1
  call void @quantum_int2char(i32 %i48, i8* %arrayidx107)
  %arrayidx108 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 5
  call void @quantum_double2char(double %i54, i8* %arrayidx108)
  br label %sw.epilog

sw.bb109:                                         ; preds = %if.end
  %arraydecay110 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p111 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay110, i32 0, i32 0
  %gp_offset112 = load i32, i32* %gp_offset_p111, align 16
  %fits_in_gp113 = icmp ule i32 %gp_offset112, 40
  br i1 %fits_in_gp113, label %vaarg.in_reg114, label %vaarg.in_mem116

vaarg.in_reg114:                                  ; preds = %sw.bb109
  %i55 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay110, i32 0, i32 3
  %reg_save_area115 = load i8*, i8** %i55, align 16
  %i56 = getelementptr i8, i8* %reg_save_area115, i32 %gp_offset112
  %i57 = bitcast i8* %i56 to i32*
  %i58 = add i32 %gp_offset112, 8
  store i32 %i58, i32* %gp_offset_p111, align 16
  br label %vaarg.end120

vaarg.in_mem116:                                  ; preds = %sw.bb109
  %overflow_arg_area_p117 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay110, i32 0, i32 2
  %overflow_arg_area118 = load i8*, i8** %overflow_arg_area_p117, align 8
  %i59 = bitcast i8* %overflow_arg_area118 to i32*
  %overflow_arg_area.next119 = getelementptr i8, i8* %overflow_arg_area118, i32 8
  store i8* %overflow_arg_area.next119, i8** %overflow_arg_area_p117, align 8
  br label %vaarg.end120

vaarg.end120:                                     ; preds = %vaarg.in_mem116, %vaarg.in_reg114
  %vaarg.addr121 = phi i32* [ %i57, %vaarg.in_reg114 ], [ %i59, %vaarg.in_mem116 ]
  %i60 = load i32, i32* %vaarg.addr121, align 4
  %arrayidx122 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 1
  call void @quantum_int2char(i32 %i60, i8* %arrayidx122)
  %arraydecay123 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %gp_offset_p124 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay123, i32 0, i32 0
  %gp_offset125 = load i32, i32* %gp_offset_p124, align 16
  %fits_in_gp126 = icmp ule i32 %gp_offset125, 40
  br i1 %fits_in_gp126, label %vaarg.in_reg127, label %vaarg.in_mem129

vaarg.in_reg127:                                  ; preds = %vaarg.end120
  %i61 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay123, i32 0, i32 3
  %reg_save_area128 = load i8*, i8** %i61, align 16
  %i62 = getelementptr i8, i8* %reg_save_area128, i32 %gp_offset125
  %i63 = bitcast i8* %i62 to i32*
  %i64 = add i32 %gp_offset125, 8
  store i32 %i64, i32* %gp_offset_p124, align 16
  br label %vaarg.end133

vaarg.in_mem129:                                  ; preds = %vaarg.end120
  %overflow_arg_area_p130 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay123, i32 0, i32 2
  %overflow_arg_area131 = load i8*, i8** %overflow_arg_area_p130, align 8
  %i65 = bitcast i8* %overflow_arg_area131 to i32*
  %overflow_arg_area.next132 = getelementptr i8, i8* %overflow_arg_area131, i32 8
  store i8* %overflow_arg_area.next132, i8** %overflow_arg_area_p130, align 8
  br label %vaarg.end133

vaarg.end133:                                     ; preds = %vaarg.in_mem129, %vaarg.in_reg127
  %vaarg.addr134 = phi i32* [ %i63, %vaarg.in_reg127 ], [ %i65, %vaarg.in_mem129 ]
  %i66 = load i32, i32* %vaarg.addr134, align 4
  %arrayidx135 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 5
  call void @quantum_int2char(i32 %i66, i8* %arrayidx135)
  %arraydecay136 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %args, i64 0, i64 0
  %fp_offset_p137 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay136, i32 0, i32 1
  %fp_offset138 = load i32, i32* %fp_offset_p137, align 4
  %fits_in_fp139 = icmp ule i32 %fp_offset138, 160
  br i1 %fits_in_fp139, label %vaarg.in_reg140, label %vaarg.in_mem142

vaarg.in_reg140:                                  ; preds = %vaarg.end133
  %i67 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay136, i32 0, i32 3
  %reg_save_area141 = load i8*, i8** %i67, align 16
  %i68 = getelementptr i8, i8* %reg_save_area141, i32 %fp_offset138
  %i69 = bitcast i8* %i68 to double*
  %i70 = add i32 %fp_offset138, 16
  store i32 %i70, i32* %fp_offset_p137, align 4
  br label %vaarg.end146

vaarg.in_mem142:                                  ; preds = %vaarg.end133
  %overflow_arg_area_p143 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %arraydecay136, i32 0, i32 2
  %overflow_arg_area144 = load i8*, i8** %overflow_arg_area_p143, align 8
  %i71 = bitcast i8* %overflow_arg_area144 to double*
  %overflow_arg_area.next145 = getelementptr i8, i8* %overflow_arg_area144, i32 8
  store i8* %overflow_arg_area.next145, i8** %overflow_arg_area_p143, align 8
  br label %vaarg.end146

vaarg.end146:                                     ; preds = %vaarg.in_mem142, %vaarg.in_reg140
  %vaarg.addr147 = phi double* [ %i69, %vaarg.in_reg140 ], [ %i71, %vaarg.in_mem142 ]
  %i72 = load double, double* %vaarg.addr147, align 8
  %arrayidx148 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 9
  call void @quantum_double2char(double %i72, i8* %arrayidx148)
  br label %sw.epilog

sw.bb149:                                         ; preds = %if.end, %if.end
  br label %sw.epilog

sw.default:                                       ; preds = %if.end
  %conv150 = zext i8 %operation to i32
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.1.30, i64 0, i64 0), i32 %conv150)
  call void @exit(i32 1) #10
  unreachable

sw.epilog:                                        ; preds = %sw.bb149, %vaarg.end146, %vaarg.end105, %vaarg.end82, %vaarg.end68, %vaarg.end28, %vaarg.end
  %size.0 = phi i32 [ 1, %sw.bb149 ], [ 17, %vaarg.end146 ], [ 13, %vaarg.end105 ], [ 5, %vaarg.end82 ], [ 13, %vaarg.end68 ], [ 9, %vaarg.end28 ], [ 9, %vaarg.end ]
  %i73 = load i64, i64* @position, align 8
  %conv151 = sext i32 %size.0 to i64
  %add = add i64 %i73, %conv151
  %div = udiv i64 %add, 65536
  %i74 = load i64, i64* @position, align 8
  %div152 = udiv i64 %i74, 65536
  %cmp = icmp ugt i64 %div, %div152
  br i1 %cmp, label %if.then154, label %if.end161

if.then154:                                       ; preds = %sw.epilog
  %i75 = load i64, i64* @allocated, align 8
  %inc = add i64 %i75, 1
  store i64 %inc, i64* @allocated, align 8
  %i76 = load i8*, i8** @objcode, align 8
  %i77 = load i64, i64* @allocated, align 8
  %mul = mul i64 %i77, 65536
  %call155 = call i8* @realloc(i8* %i76, i64 %mul) #9
  store i8* %call155, i8** @objcode, align 8
  %i78 = load i8*, i8** @objcode, align 8
  %tobool156 = icmp ne i8* %i78, null
  br i1 %tobool156, label %if.end159, label %if.then157

if.then157:                                       ; preds = %if.then154
  %call158 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([45 x i8], [45 x i8]* @.str.2.31, i64 0, i64 0))
  call void @exit(i32 1) #10
  unreachable

if.end159:                                        ; preds = %if.then154
  %call160 = call i64 @quantum_memman(i64 65536)
  br label %if.end161

if.end161:                                        ; preds = %if.end159, %sw.epilog
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end161
  %i.0 = phi i32 [ 0, %if.end161 ], [ %inc167, %for.inc ]
  %cmp162 = icmp slt i32 %i.0, %size.0
  br i1 %cmp162, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %idxprom = sext i32 %i.0 to i64
  %arrayidx164 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 %idxprom
  %i79 = load i8, i8* %arrayidx164, align 1
  %i80 = load i8*, i8** @objcode, align 8
  %i81 = load i64, i64* @position, align 8
  %arrayidx165 = getelementptr inbounds i8, i8* %i80, i64 %i81
  store i8 %i79, i8* %arrayidx165, align 1
  %i82 = load i64, i64* @position, align 8
  %inc166 = add i64 %i82, 1
  store i64 %inc166, i64* @position, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc167 = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %return

return:                                           ; preds = %for.end, %if.then
  %retval.0 = phi i32 [ 1, %for.end ], [ 0, %if.then ]
  ret i32 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_objcode_write(i8* %file) #0 {
entry:
  %i = load i32, i32* @opstatus, align 4
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %i1 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %call = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %i1, i8* getelementptr inbounds ([74 x i8], [74 x i8]* @.str.3.32, i64 0, i64 0))
  br label %return

if.end:                                           ; preds = %entry
  %tobool1 = icmp ne i8* %file, null
  br i1 %tobool1, label %if.end3, label %if.then2

if.then2:                                         ; preds = %if.end
  %i2 = load i8*, i8** @globalfile, align 8
  br label %if.end3

if.end3:                                          ; preds = %if.then2, %if.end
  %file.addr.0 = phi i8* [ %file, %if.end ], [ %i2, %if.then2 ]
  %call4 = call noalias %struct._IO_FILE* @fopen(i8* %file.addr.0, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.4.33, i64 0, i64 0))
  %cmp = icmp eq %struct._IO_FILE* %call4, null
  br i1 %cmp, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end3
  br label %return

if.end6:                                          ; preds = %if.end3
  %i3 = load i8*, i8** @objcode, align 8
  %i4 = load i64, i64* @position, align 8
  %call7 = call i64 @fwrite(i8* %i3, i64 %i4, i64 1, %struct._IO_FILE* %call4)
  %call8 = call i32 @fclose(%struct._IO_FILE* %call4)
  br label %return

return:                                           ; preds = %if.end6, %if.then5, %if.then
  %retval.0 = phi i32 [ -1, %if.then5 ], [ 0, %if.end6 ], [ 1, %if.then ]
  ret i32 %retval.0
}

declare dso_local i32 @fprintf(%struct._IO_FILE*, i8*, ...) #4

declare dso_local noalias %struct._IO_FILE* @fopen(i8*, i8*) #4

declare dso_local i64 @fwrite(i8*, i64, i64, %struct._IO_FILE*) #4

declare dso_local i32 @fclose(%struct._IO_FILE*) #4

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_objcode_file(i8* %file) #0 {
entry:
  store i8* %file, i8** @globalfile, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_objcode_exit(i8* %file) #0 {
entry:
  %call = call i32 @quantum_objcode_write(i8* null)
  call void @quantum_objcode_stop()
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_objcode_run(i8* %file, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %buf = alloca [80 x i8], align 16
  %tmp = alloca %struct.quantum_reg_struct, align 8
  %call = call noalias %struct._IO_FILE* @fopen(i8* %file, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.5, i64 0, i64 0))
  %tobool = icmp ne %struct._IO_FILE* %call, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %i = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %call1 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %i, i8* getelementptr inbounds ([41 x i8], [41 x i8]* @.str.6, i64 0, i64 0), i8* %file)
  call void @perror(i8* null)
  br label %return

if.end:                                           ; preds = %entry
  br label %for.cond

for.cond:                                         ; preds = %for.inc93, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc94, %for.inc93 ]
  %call2 = call i32 @feof(%struct._IO_FILE* %call) #9
  %tobool3 = icmp ne i32 %call2, 0
  %lnot = xor i1 %tobool3, true
  br i1 %lnot, label %for.body, label %for.end95

for.body:                                         ; preds = %for.cond
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ 0, %for.body ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %j.0, 80
  br i1 %cmp, label %for.body5, label %for.end

for.body5:                                        ; preds = %for.cond4
  %idxprom = sext i32 %j.0 to i64
  %arrayidx = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 %idxprom
  store i8 0, i8* %arrayidx, align 1
  br label %for.inc

for.inc:                                          ; preds = %for.body5
  %inc = add nsw i32 %j.0, 1
  br label %for.cond4

for.end:                                          ; preds = %for.cond4
  %call6 = call i32 @fgetc(%struct._IO_FILE* %call)
  %conv = trunc i32 %call6 to i8
  %conv7 = zext i8 %conv to i32
  switch i32 %conv7, label %sw.default [
    i32 0, label %sw.bb
    i32 1, label %sw.bb11
    i32 12, label %sw.bb11
    i32 2, label %sw.bb23
    i32 3, label %sw.bb36
    i32 4, label %sw.bb36
    i32 5, label %sw.bb36
    i32 6, label %sw.bb36
    i32 129, label %sw.bb36
    i32 130, label %sw.bb36
    i32 14, label %sw.bb36
    i32 7, label %sw.bb52
    i32 8, label %sw.bb52
    i32 9, label %sw.bb52
    i32 10, label %sw.bb52
    i32 11, label %sw.bb52
    i32 13, label %sw.bb73
    i32 128, label %sw.bb87
    i32 255, label %sw.bb89
  ]

sw.bb:                                            ; preds = %for.end
  %arraydecay = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call8 = call i64 @fread(i8* %arraydecay, i64 8, i64 1, %struct._IO_FILE* %call)
  %arraydecay9 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call10 = call i64 @quantum_char2mu(i8* %arraydecay9)
  call void @quantum_new_qureg(%struct.quantum_reg_struct* sret(%struct.quantum_reg_struct) align 8 %tmp, i64 %call10, i32 12)
  %i1 = bitcast %struct.quantum_reg_struct* %reg to i8*
  %i2 = bitcast %struct.quantum_reg_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i1, i8* align 8 %i2, i64 32, i1 false)
  br label %sw.epilog92

sw.bb11:                                          ; preds = %for.end, %for.end
  %arraydecay12 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call13 = call i64 @fread(i8* %arraydecay12, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay14 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call15 = call i32 @quantum_char2int(i8* %arraydecay14)
  %arraydecay16 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call17 = call i64 @fread(i8* %arraydecay16, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay18 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call19 = call i32 @quantum_char2int(i8* %arraydecay18)
  %conv20 = zext i8 %conv to i32
  switch i32 %conv20, label %sw.epilog [
    i32 1, label %sw.bb21
    i32 12, label %sw.bb22
  ]

sw.bb21:                                          ; preds = %sw.bb11
  call void @quantum_cnot(i32 %call15, i32 %call19, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog

sw.bb22:                                          ; preds = %sw.bb11
  call void @quantum_cond_phase(i32 %call15, i32 %call19, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog

sw.epilog:                                        ; preds = %sw.bb22, %sw.bb21, %sw.bb11
  br label %sw.epilog92

sw.bb23:                                          ; preds = %for.end
  %arraydecay24 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call25 = call i64 @fread(i8* %arraydecay24, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay26 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call27 = call i32 @quantum_char2int(i8* %arraydecay26)
  %arraydecay28 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call29 = call i64 @fread(i8* %arraydecay28, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay30 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call31 = call i32 @quantum_char2int(i8* %arraydecay30)
  %arraydecay32 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call33 = call i64 @fread(i8* %arraydecay32, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay34 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call35 = call i32 @quantum_char2int(i8* %arraydecay34)
  call void @quantum_toffoli(i32 %call27, i32 %call31, i32 %call35, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog92

sw.bb36:                                          ; preds = %for.end, %for.end, %for.end, %for.end, %for.end, %for.end, %for.end
  %arraydecay37 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call38 = call i64 @fread(i8* %arraydecay37, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay39 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call40 = call i32 @quantum_char2int(i8* %arraydecay39)
  %conv41 = zext i8 %conv to i32
  switch i32 %conv41, label %sw.epilog51 [
    i32 3, label %sw.bb42
    i32 4, label %sw.bb43
    i32 5, label %sw.bb44
    i32 6, label %sw.bb45
    i32 129, label %sw.bb46
    i32 130, label %sw.bb48
    i32 14, label %sw.bb50
  ]

sw.bb42:                                          ; preds = %sw.bb36
  call void @quantum_sigma_x(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.bb43:                                          ; preds = %sw.bb36
  call void @quantum_sigma_y(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.bb44:                                          ; preds = %sw.bb36
  call void @quantum_sigma_z(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.bb45:                                          ; preds = %sw.bb36
  call void @quantum_hadamard(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.bb46:                                          ; preds = %sw.bb36
  %call47 = call i32 @quantum_bmeasure(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.bb48:                                          ; preds = %sw.bb36
  %call49 = call i32 @quantum_bmeasure_bitpreserve(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.bb50:                                          ; preds = %sw.bb36
  call void @quantum_swaptheleads(i32 %call40, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog51

sw.epilog51:                                      ; preds = %sw.bb50, %sw.bb48, %sw.bb46, %sw.bb45, %sw.bb44, %sw.bb43, %sw.bb42, %sw.bb36
  br label %sw.epilog92

sw.bb52:                                          ; preds = %for.end, %for.end, %for.end, %for.end, %for.end
  %arraydecay53 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call54 = call i64 @fread(i8* %arraydecay53, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay55 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call56 = call i32 @quantum_char2int(i8* %arraydecay55)
  %arraydecay57 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call58 = call i64 @fread(i8* %arraydecay57, i64 8, i64 1, %struct._IO_FILE* %call)
  %arraydecay59 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call60 = call double @quantum_char2double(i8* %arraydecay59)
  %conv61 = zext i8 %conv to i32
  switch i32 %conv61, label %sw.epilog72 [
    i32 7, label %sw.bb62
    i32 8, label %sw.bb64
    i32 9, label %sw.bb66
    i32 10, label %sw.bb68
    i32 11, label %sw.bb70
  ]

sw.bb62:                                          ; preds = %sw.bb52
  %conv63 = fptrunc double %call60 to float
  call void @quantum_r_x(i32 %call56, float %conv63, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog72

sw.bb64:                                          ; preds = %sw.bb52
  %conv65 = fptrunc double %call60 to float
  call void @quantum_r_y(i32 %call56, float %conv65, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog72

sw.bb66:                                          ; preds = %sw.bb52
  %conv67 = fptrunc double %call60 to float
  call void @quantum_r_z(i32 %call56, float %conv67, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog72

sw.bb68:                                          ; preds = %sw.bb52
  %conv69 = fptrunc double %call60 to float
  call void @quantum_phase_kick(i32 %call56, float %conv69, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog72

sw.bb70:                                          ; preds = %sw.bb52
  %conv71 = fptrunc double %call60 to float
  call void @quantum_phase_scale(i32 %call56, float %conv71, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog72

sw.epilog72:                                      ; preds = %sw.bb70, %sw.bb68, %sw.bb66, %sw.bb64, %sw.bb62, %sw.bb52
  br label %sw.epilog92

sw.bb73:                                          ; preds = %for.end
  %arraydecay74 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call75 = call i64 @fread(i8* %arraydecay74, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay76 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call77 = call i32 @quantum_char2int(i8* %arraydecay76)
  %arraydecay78 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call79 = call i64 @fread(i8* %arraydecay78, i64 4, i64 1, %struct._IO_FILE* %call)
  %arraydecay80 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call81 = call i32 @quantum_char2int(i8* %arraydecay80)
  %arraydecay82 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call83 = call i64 @fread(i8* %arraydecay82, i64 8, i64 1, %struct._IO_FILE* %call)
  %arraydecay84 = getelementptr inbounds [80 x i8], [80 x i8]* %buf, i64 0, i64 0
  %call85 = call double @quantum_char2double(i8* %arraydecay84)
  %conv86 = fptrunc double %call85 to float
  call void @quantum_cond_phase_kick(i32 %call77, i32 %call81, float %conv86, %struct.quantum_reg_struct* %reg)
  br label %sw.epilog92

sw.bb87:                                          ; preds = %for.end
  %call88 = call i64 @quantum_measure(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg)
  br label %sw.epilog92

sw.bb89:                                          ; preds = %for.end
  br label %sw.epilog92

sw.default:                                       ; preds = %for.end
  %i3 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %conv90 = zext i8 %conv to i32
  %call91 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %i3, i8* getelementptr inbounds ([28 x i8], [28 x i8]* @.str.7, i64 0, i64 0), i32 %i.0, i32 %conv90)
  br label %return

sw.epilog92:                                      ; preds = %sw.bb89, %sw.bb87, %sw.bb73, %sw.epilog72, %sw.epilog51, %sw.bb23, %sw.epilog, %sw.bb
  br label %for.inc93

for.inc93:                                        ; preds = %sw.epilog92
  %inc94 = add nsw i32 %i.0, 1
  br label %for.cond

for.end95:                                        ; preds = %for.cond
  %call96 = call i32 @fclose(%struct._IO_FILE* %call)
  br label %return

return:                                           ; preds = %for.end95, %sw.default, %if.then
  ret void
}

declare dso_local void @perror(i8*) #4

; Function Attrs: nounwind
declare dso_local i32 @feof(%struct._IO_FILE*) #3

declare dso_local i32 @fgetc(%struct._IO_FILE*) #4

declare dso_local i64 @fread(i8*, i64, i64, %struct._IO_FILE*) #4

; Function Attrs: noinline nounwind uwtable
define dso_local void @emul(i32 %a, i32 %L, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %sub = sub nsw i32 %width, 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ %sub, %entry ], [ %dec, %for.inc ]
  %cmp = icmp sge i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %shr = ashr i32 %a, %i.0
  %and = and i32 %shr, 1
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  %mul = mul nsw i32 2, %width
  %add = add nsw i32 %mul, 2
  %add1 = add nsw i32 %width, %i.0
  call void @quantum_toffoli(i32 %add, i32 %L, i32 %add1, %struct.quantum_reg_struct* %reg)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @muln(i32 %N, i32 %a, i32 %ctl, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %mul = mul nsw i32 2, %width
  %add = add nsw i32 %mul, 1
  %mul1 = mul nsw i32 2, %width
  %add2 = add nsw i32 %mul1, 2
  call void @quantum_toffoli(i32 %ctl, i32 %add2, i32 %add, %struct.quantum_reg_struct* %reg)
  %rem = srem i32 %a, %N
  call void @emul(i32 %rem, i32 %add, i32 %width, %struct.quantum_reg_struct* %reg)
  %mul3 = mul nsw i32 2, %width
  %add4 = add nsw i32 %mul3, 2
  call void @quantum_toffoli(i32 %ctl, i32 %add4, i32 %add, %struct.quantum_reg_struct* %reg)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 1, %entry ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %i.0, %width
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %mul5 = mul nsw i32 2, %width
  %add6 = add nsw i32 %mul5, 2
  %add7 = add nsw i32 %add6, %i.0
  call void @quantum_toffoli(i32 %ctl, i32 %add7, i32 %add, %struct.quantum_reg_struct* %reg)
  %shl = shl i32 1, %i.0
  %mul8 = mul nsw i32 %shl, %a
  %rem9 = srem i32 %mul8, %N
  call void @add_mod_n(i32 %N, i32 %rem9, i32 %width, %struct.quantum_reg_struct* %reg)
  %mul10 = mul nsw i32 2, %width
  %add11 = add nsw i32 %mul10, 2
  %add12 = add nsw i32 %add11, %i.0
  call void @quantum_toffoli(i32 %ctl, i32 %add12, i32 %add, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @muln_inv(i32 %N, i32 %a, i32 %ctl, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %mul = mul nsw i32 2, %width
  %add = add nsw i32 %mul, 1
  %call = call i32 @quantum_inverse_mod(i32 %N, i32 %a)
  %sub = sub nsw i32 %width, 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ %sub, %entry ], [ %dec, %for.inc ]
  %cmp = icmp sgt i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %mul1 = mul nsw i32 2, %width
  %add2 = add nsw i32 %mul1, 2
  %add3 = add nsw i32 %add2, %i.0
  call void @quantum_toffoli(i32 %ctl, i32 %add3, i32 %add, %struct.quantum_reg_struct* %reg)
  %shl = shl i32 1, %i.0
  %mul4 = mul nsw i32 %shl, %call
  %rem = srem i32 %mul4, %N
  %sub5 = sub nsw i32 %N, %rem
  call void @add_mod_n(i32 %N, i32 %sub5, i32 %width, %struct.quantum_reg_struct* %reg)
  %mul6 = mul nsw i32 2, %width
  %add7 = add nsw i32 %mul6, 2
  %add8 = add nsw i32 %add7, %i.0
  call void @quantum_toffoli(i32 %ctl, i32 %add8, i32 %add, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %mul9 = mul nsw i32 2, %width
  %add10 = add nsw i32 %mul9, 2
  call void @quantum_toffoli(i32 %ctl, i32 %add10, i32 %add, %struct.quantum_reg_struct* %reg)
  %rem11 = srem i32 %call, %N
  call void @emul(i32 %rem11, i32 %add, i32 %width, %struct.quantum_reg_struct* %reg)
  %mul12 = mul nsw i32 2, %width
  %add13 = add nsw i32 %mul12, 2
  call void @quantum_toffoli(i32 %ctl, i32 %add13, i32 %add, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @mul_mod_n(i32 %N, i32 %a, i32 %ctl, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  call void @muln(i32 %N, i32 %a, i32 %ctl, i32 %width, %struct.quantum_reg_struct* %reg)
  call void @quantum_swaptheleads_omuln_controlled(i32 %ctl, i32 %width, %struct.quantum_reg_struct* %reg)
  call void @muln_inv(i32 %N, i32 %a, i32 %ctl, i32 %width, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_qec_set_status(i32 %stype, i32 %swidth) #0 {
entry:
  store i32 %stype, i32* @type, align 4
  store i32 %swidth, i32* @width, align 4
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_qec_get_status(i32* %ptype, i32* %pwidth) #0 {
entry:
  %tobool = icmp ne i32* %ptype, null
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %i = load i32, i32* @type, align 4
  store i32 %i, i32* %ptype, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %tobool1 = icmp ne i32* %pwidth, null
  br i1 %tobool1, label %if.then2, label %if.end3

if.then2:                                         ; preds = %if.end
  %i1 = load i32, i32* @width, align 4
  store i32 %i1, i32* %pwidth, align 4
  br label %if.end3

if.end3:                                          ; preds = %if.then2, %if.end
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_qec_encode(i32 %type, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %call = call float (...) bitcast (float ()* @quantum_get_decoherence to float (...)*)()
  call void @quantum_set_decoherence(float 0.000000e+00)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %width1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i = load i32, i32* %width1, align 8
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %width2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i1 = load i32, i32* %width2, align 8
  %sub = sub nsw i32 %i1, 1
  %cmp3 = icmp eq i32 %i.0, %sub
  br i1 %cmp3, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  call void @quantum_set_decoherence(float %call)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %cmp4 = icmp slt i32 %i.0, %width
  br i1 %cmp4, label %if.then5, label %if.else

if.then5:                                         ; preds = %if.end
  %width6 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i2 = load i32, i32* %width6, align 8
  %add = add nsw i32 %i2, %i.0
  call void @quantum_hadamard(i32 %add, %struct.quantum_reg_struct* %reg)
  %width7 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i3 = load i32, i32* %width7, align 8
  %mul = mul nsw i32 2, %i3
  %add8 = add nsw i32 %mul, %i.0
  call void @quantum_hadamard(i32 %add8, %struct.quantum_reg_struct* %reg)
  %width9 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i4 = load i32, i32* %width9, align 8
  %add10 = add nsw i32 %i4, %i.0
  call void @quantum_cnot(i32 %add10, i32 %i.0, %struct.quantum_reg_struct* %reg)
  %width11 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i5 = load i32, i32* %width11, align 8
  %mul12 = mul nsw i32 2, %i5
  %add13 = add nsw i32 %mul12, %i.0
  call void @quantum_cnot(i32 %add13, i32 %i.0, %struct.quantum_reg_struct* %reg)
  br label %if.end19

if.else:                                          ; preds = %if.end
  %width14 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i6 = load i32, i32* %width14, align 8
  %add15 = add nsw i32 %i6, %i.0
  call void @quantum_cnot(i32 %i.0, i32 %add15, %struct.quantum_reg_struct* %reg)
  %width16 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i7 = load i32, i32* %width16, align 8
  %mul17 = mul nsw i32 2, %i7
  %add18 = add nsw i32 %mul17, %i.0
  call void @quantum_cnot(i32 %i.0, i32 %add18, %struct.quantum_reg_struct* %reg)
  br label %if.end19

if.end19:                                         ; preds = %if.else, %if.then5
  br label %for.inc

for.inc:                                          ; preds = %if.end19
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %width20 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i8 = load i32, i32* %width20, align 8
  call void @quantum_qec_set_status(i32 1, i32 %i8)
  %width21 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i9 = load i32, i32* %width21, align 8
  %mul22 = mul nsw i32 %i9, 3
  store i32 %mul22, i32* %width21, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_qec_decode(i32 %type, i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %call = call float (...) bitcast (float ()* @quantum_get_decoherence to float (...)*)()
  call void @quantum_set_decoherence(float 0.000000e+00)
  %width1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i = load i32, i32* %width1, align 8
  %div = sdiv i32 %i, 3
  call void @quantum_qec_set_status(i32 0, i32 0)
  %width2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i1 = load i32, i32* %width2, align 8
  %div3 = sdiv i32 %i1, 3
  %sub = sub nsw i32 %div3, 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ %sub, %entry ], [ %dec, %for.inc ]
  %cmp = icmp sge i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %cmp4 = icmp eq i32 %i.0, 0
  br i1 %cmp4, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  call void @quantum_set_decoherence(float %call)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %cmp5 = icmp slt i32 %i.0, %width
  br i1 %cmp5, label %if.then6, label %if.else

if.then6:                                         ; preds = %if.end
  %mul = mul nsw i32 2, %div
  %add = add nsw i32 %mul, %i.0
  call void @quantum_cnot(i32 %add, i32 %i.0, %struct.quantum_reg_struct* %reg)
  %add7 = add nsw i32 %div, %i.0
  call void @quantum_cnot(i32 %add7, i32 %i.0, %struct.quantum_reg_struct* %reg)
  %mul8 = mul nsw i32 2, %div
  %add9 = add nsw i32 %mul8, %i.0
  call void @quantum_hadamard(i32 %add9, %struct.quantum_reg_struct* %reg)
  %add10 = add nsw i32 %div, %i.0
  call void @quantum_hadamard(i32 %add10, %struct.quantum_reg_struct* %reg)
  br label %if.end14

if.else:                                          ; preds = %if.end
  %mul11 = mul nsw i32 2, %div
  %add12 = add nsw i32 %mul11, %i.0
  call void @quantum_cnot(i32 %i.0, i32 %add12, %struct.quantum_reg_struct* %reg)
  %add13 = add nsw i32 %div, %i.0
  call void @quantum_cnot(i32 %i.0, i32 %add13, %struct.quantum_reg_struct* %reg)
  br label %if.end14

if.end14:                                         ; preds = %if.else, %if.then6
  br label %for.inc

for.inc:                                          ; preds = %if.end14
  %dec = add nsw i32 %i.0, -1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond15

for.cond15:                                       ; preds = %for.inc30, %for.end
  %i.1 = phi i32 [ 1, %for.end ], [ %inc, %for.inc30 ]
  %cmp16 = icmp sle i32 %i.1, %div
  br i1 %cmp16, label %for.body17, label %for.end31

for.body17:                                       ; preds = %for.cond15
  %call18 = call i32 @quantum_bmeasure(i32 %div, %struct.quantum_reg_struct* %reg)
  %mul19 = mul nsw i32 2, %div
  %sub20 = sub nsw i32 %mul19, %i.1
  %call21 = call i32 @quantum_bmeasure(i32 %sub20, %struct.quantum_reg_struct* %reg)
  %cmp22 = icmp eq i32 %call18, 1
  br i1 %cmp22, label %land.lhs.true, label %if.end29

land.lhs.true:                                    ; preds = %for.body17
  %cmp23 = icmp eq i32 %call21, 1
  br i1 %cmp23, label %land.lhs.true24, label %if.end29

land.lhs.true24:                                  ; preds = %land.lhs.true
  %sub25 = sub nsw i32 %i.1, 1
  %cmp26 = icmp slt i32 %sub25, %width
  br i1 %cmp26, label %if.then27, label %if.end29

if.then27:                                        ; preds = %land.lhs.true24
  %sub28 = sub nsw i32 %i.1, 1
  call void @quantum_sigma_z(i32 %sub28, %struct.quantum_reg_struct* %reg)
  br label %if.end29

if.end29:                                         ; preds = %if.then27, %land.lhs.true24, %land.lhs.true, %for.body17
  br label %for.inc30

for.inc30:                                        ; preds = %if.end29
  %inc = add nsw i32 %i.1, 1
  br label %for.cond15

for.end31:                                        ; preds = %for.cond15
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @quantum_qec_counter(i32 %inc, i32 %frequency, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %cmp = icmp sgt i32 %inc, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %i = load i32, i32* @quantum_qec_counter.counter, align 4
  %add = add nsw i32 %i, %inc
  store i32 %add, i32* @quantum_qec_counter.counter, align 4
  br label %if.end3

if.else:                                          ; preds = %entry
  %cmp1 = icmp slt i32 %inc, 0
  br i1 %cmp1, label %if.then2, label %if.end

if.then2:                                         ; preds = %if.else
  store i32 0, i32* @quantum_qec_counter.counter, align 4
  br label %if.end

if.end:                                           ; preds = %if.then2, %if.else
  br label %if.end3

if.end3:                                          ; preds = %if.end, %if.then
  %cmp4 = icmp sgt i32 %frequency, 0
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end3
  store i32 %frequency, i32* @quantum_qec_counter.freq, align 4
  br label %if.end6

if.end6:                                          ; preds = %if.then5, %if.end3
  %i1 = load i32, i32* @quantum_qec_counter.counter, align 4
  %i2 = load i32, i32* @quantum_qec_counter.freq, align 4
  %cmp7 = icmp sge i32 %i1, %i2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end6
  store i32 0, i32* @quantum_qec_counter.counter, align 4
  %i3 = load i32, i32* @type, align 4
  %i4 = load i32, i32* @width, align 4
  call void @quantum_qec_decode(i32 %i3, i32 %i4, %struct.quantum_reg_struct* %reg)
  %i5 = load i32, i32* @type, align 4
  %i6 = load i32, i32* @width, align 4
  call void @quantum_qec_encode(i32 %i5, i32 %i6, %struct.quantum_reg_struct* %reg)
  br label %if.end9

if.end9:                                          ; preds = %if.then8, %if.end6
  %i7 = load i32, i32* @quantum_qec_counter.counter, align 4
  ret i32 %i7
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_sigma_x_ft(i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %i = load i32, i32* @type, align 4
  store i32 0, i32* @type, align 4
  %call = call float (...) bitcast (float ()* @quantum_get_decoherence to float (...)*)()
  call void @quantum_set_decoherence(float 0.000000e+00)
  call void @quantum_sigma_x(i32 %target, %struct.quantum_reg_struct* %reg)
  %i1 = load i32, i32* @width, align 4
  %add = add nsw i32 %target, %i1
  call void @quantum_sigma_x(i32 %add, %struct.quantum_reg_struct* %reg)
  call void @quantum_set_decoherence(float %call)
  %i2 = load i32, i32* @width, align 4
  %mul = mul nsw i32 2, %i2
  %add1 = add nsw i32 %target, %mul
  call void @quantum_sigma_x(i32 %add1, %struct.quantum_reg_struct* %reg)
  %call2 = call i32 @quantum_qec_counter(i32 1, i32 0, %struct.quantum_reg_struct* %reg)
  store i32 %i, i32* @type, align 4
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_cnot_ft(i32 %control, i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %i = load i32, i32* @type, align 4
  store i32 0, i32* @type, align 4
  %call = call float (...) bitcast (float ()* @quantum_get_decoherence to float (...)*)()
  call void @quantum_set_decoherence(float 0.000000e+00)
  call void @quantum_cnot(i32 %control, i32 %target, %struct.quantum_reg_struct* %reg)
  %i1 = load i32, i32* @width, align 4
  %add = add nsw i32 %control, %i1
  %i2 = load i32, i32* @width, align 4
  %add1 = add nsw i32 %target, %i2
  call void @quantum_cnot(i32 %add, i32 %add1, %struct.quantum_reg_struct* %reg)
  call void @quantum_set_decoherence(float %call)
  %i3 = load i32, i32* @width, align 4
  %mul = mul nsw i32 2, %i3
  %add2 = add nsw i32 %control, %mul
  %i4 = load i32, i32* @width, align 4
  %mul3 = mul nsw i32 2, %i4
  %add4 = add nsw i32 %target, %mul3
  call void @quantum_cnot(i32 %add2, i32 %add4, %struct.quantum_reg_struct* %reg)
  %call5 = call i32 @quantum_qec_counter(i32 1, i32 0, %struct.quantum_reg_struct* %reg)
  store i32 %i, i32* @type, align 4
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_toffoli_ft(i32 %control1, i32 %control2, i32 %target, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %sh_prom = zext i32 %target to i64
  %shl = shl i64 1, %sh_prom
  %i = load i32, i32* @width, align 4
  %add = add nsw i32 %target, %i
  %sh_prom1 = zext i32 %add to i64
  %shl2 = shl i64 1, %sh_prom1
  %add3 = add i64 %shl, %shl2
  %i1 = load i32, i32* @width, align 4
  %mul = mul nsw i32 2, %i1
  %add4 = add nsw i32 %target, %mul
  %sh_prom5 = zext i32 %add4 to i64
  %shl6 = shl i64 1, %sh_prom5
  %add7 = add i64 %add3, %shl6
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i2 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i2
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i4 = load i64, i64* %state, align 8
  %sh_prom8 = zext i32 %control1 to i64
  %shl9 = shl i64 1, %sh_prom8
  %and = and i64 %i4, %shl9
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  %c1.0 = phi i32 [ 1, %if.then ], [ 0, %for.body ]
  %node10 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i5 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node10, align 8
  %idxprom11 = sext i32 %i.0 to i64
  %arrayidx12 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i5, i64 %idxprom11
  %state13 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx12, i32 0, i32 1
  %i6 = load i64, i64* %state13, align 8
  %i7 = load i32, i32* @width, align 4
  %add14 = add nsw i32 %control1, %i7
  %sh_prom15 = zext i32 %add14 to i64
  %shl16 = shl i64 1, %sh_prom15
  %and17 = and i64 %i6, %shl16
  %tobool18 = icmp ne i64 %and17, 0
  br i1 %tobool18, label %if.then19, label %if.end20

if.then19:                                        ; preds = %if.end
  %xor = xor i32 %c1.0, 1
  br label %if.end20

if.end20:                                         ; preds = %if.then19, %if.end
  %c1.1 = phi i32 [ %xor, %if.then19 ], [ %c1.0, %if.end ]
  %node21 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node21, align 8
  %idxprom22 = sext i32 %i.0 to i64
  %arrayidx23 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i8, i64 %idxprom22
  %state24 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx23, i32 0, i32 1
  %i9 = load i64, i64* %state24, align 8
  %i10 = load i32, i32* @width, align 4
  %mul25 = mul nsw i32 2, %i10
  %add26 = add nsw i32 %control1, %mul25
  %sh_prom27 = zext i32 %add26 to i64
  %shl28 = shl i64 1, %sh_prom27
  %and29 = and i64 %i9, %shl28
  %tobool30 = icmp ne i64 %and29, 0
  br i1 %tobool30, label %if.then31, label %if.end33

if.then31:                                        ; preds = %if.end20
  %xor32 = xor i32 %c1.1, 1
  br label %if.end33

if.end33:                                         ; preds = %if.then31, %if.end20
  %c1.2 = phi i32 [ %xor32, %if.then31 ], [ %c1.1, %if.end20 ]
  %node34 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i11 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node34, align 8
  %idxprom35 = sext i32 %i.0 to i64
  %arrayidx36 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i11, i64 %idxprom35
  %state37 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx36, i32 0, i32 1
  %i12 = load i64, i64* %state37, align 8
  %sh_prom38 = zext i32 %control2 to i64
  %shl39 = shl i64 1, %sh_prom38
  %and40 = and i64 %i12, %shl39
  %tobool41 = icmp ne i64 %and40, 0
  br i1 %tobool41, label %if.then42, label %if.end43

if.then42:                                        ; preds = %if.end33
  br label %if.end43

if.end43:                                         ; preds = %if.then42, %if.end33
  %c2.0 = phi i32 [ 1, %if.then42 ], [ 0, %if.end33 ]
  %node44 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i13 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node44, align 8
  %idxprom45 = sext i32 %i.0 to i64
  %arrayidx46 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i13, i64 %idxprom45
  %state47 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx46, i32 0, i32 1
  %i14 = load i64, i64* %state47, align 8
  %i15 = load i32, i32* @width, align 4
  %add48 = add nsw i32 %control2, %i15
  %sh_prom49 = zext i32 %add48 to i64
  %shl50 = shl i64 1, %sh_prom49
  %and51 = and i64 %i14, %shl50
  %tobool52 = icmp ne i64 %and51, 0
  br i1 %tobool52, label %if.then53, label %if.end55

if.then53:                                        ; preds = %if.end43
  %xor54 = xor i32 %c2.0, 1
  br label %if.end55

if.end55:                                         ; preds = %if.then53, %if.end43
  %c2.1 = phi i32 [ %xor54, %if.then53 ], [ %c2.0, %if.end43 ]
  %node56 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i16 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node56, align 8
  %idxprom57 = sext i32 %i.0 to i64
  %arrayidx58 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i16, i64 %idxprom57
  %state59 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx58, i32 0, i32 1
  %i17 = load i64, i64* %state59, align 8
  %i18 = load i32, i32* @width, align 4
  %mul60 = mul nsw i32 2, %i18
  %add61 = add nsw i32 %control2, %mul60
  %sh_prom62 = zext i32 %add61 to i64
  %shl63 = shl i64 1, %sh_prom62
  %and64 = and i64 %i17, %shl63
  %tobool65 = icmp ne i64 %and64, 0
  br i1 %tobool65, label %if.then66, label %if.end68

if.then66:                                        ; preds = %if.end55
  %xor67 = xor i32 %c2.1, 1
  br label %if.end68

if.end68:                                         ; preds = %if.then66, %if.end55
  %c2.2 = phi i32 [ %xor67, %if.then66 ], [ %c2.1, %if.end55 ]
  %cmp69 = icmp eq i32 %c1.2, 1
  br i1 %cmp69, label %land.lhs.true, label %if.end81

land.lhs.true:                                    ; preds = %if.end68
  %cmp70 = icmp eq i32 %c2.2, 1
  br i1 %cmp70, label %if.then71, label %if.end81

if.then71:                                        ; preds = %land.lhs.true
  %node72 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i19 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node72, align 8
  %idxprom73 = sext i32 %i.0 to i64
  %arrayidx74 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i19, i64 %idxprom73
  %state75 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx74, i32 0, i32 1
  %i20 = load i64, i64* %state75, align 8
  %xor76 = xor i64 %i20, %add7
  %node77 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i21 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node77, align 8
  %idxprom78 = sext i32 %i.0 to i64
  %arrayidx79 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i21, i64 %idxprom78
  %state80 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx79, i32 0, i32 1
  store i64 %xor76, i64* %state80, align 8
  br label %if.end81

if.end81:                                         ; preds = %if.then71, %land.lhs.true, %if.end68
  br label %for.inc

for.inc:                                          ; preds = %if.end81
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  call void @quantum_decohere(%struct.quantum_reg_struct* %reg)
  %call = call i32 @quantum_qec_counter(i32 1, i32 0, %struct.quantum_reg_struct* %reg)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_qft(i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %sub = sub nsw i32 %width, 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc5, %entry
  %i.0 = phi i32 [ %sub, %entry ], [ %dec6, %for.inc5 ]
  %cmp = icmp sge i32 %i.0, 0
  br i1 %cmp, label %for.body, label %for.end7

for.body:                                         ; preds = %for.cond
  %sub1 = sub nsw i32 %width, 1
  br label %for.cond2

for.cond2:                                        ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ %sub1, %for.body ], [ %dec, %for.inc ]
  %cmp3 = icmp sgt i32 %j.0, %i.0
  br i1 %cmp3, label %for.body4, label %for.end

for.body4:                                        ; preds = %for.cond2
  call void @quantum_cond_phase(i32 %j.0, i32 %i.0, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body4
  %dec = add nsw i32 %j.0, -1
  br label %for.cond2

for.end:                                          ; preds = %for.cond2
  call void @quantum_hadamard(i32 %i.0, %struct.quantum_reg_struct* %reg)
  br label %for.inc5

for.inc5:                                         ; preds = %for.end
  %dec6 = add nsw i32 %i.0, -1
  br label %for.cond

for.end7:                                         ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_qft_inv(i32 %width, %struct.quantum_reg_struct* %reg) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc4, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc5, %for.inc4 ]
  %cmp = icmp slt i32 %i.0, %width
  br i1 %cmp, label %for.body, label %for.end6

for.body:                                         ; preds = %for.cond
  call void @quantum_hadamard(i32 %i.0, %struct.quantum_reg_struct* %reg)
  %add = add nsw i32 %i.0, 1
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ %add, %for.body ], [ %inc, %for.inc ]
  %cmp2 = icmp slt i32 %j.0, %width
  br i1 %cmp2, label %for.body3, label %for.end

for.body3:                                        ; preds = %for.cond1
  call void @quantum_cond_phase_inv(i32 %j.0, i32 %i.0, %struct.quantum_reg_struct* %reg)
  br label %for.inc

for.inc:                                          ; preds = %for.body3
  %inc = add nsw i32 %j.0, 1
  br label %for.cond1

for.end:                                          ; preds = %for.cond1
  br label %for.inc4

for.inc4:                                         ; preds = %for.end
  %inc5 = add nsw i32 %i.0, 1
  br label %for.cond

for.end6:                                         ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_matrix2qureg(%struct.quantum_reg_struct* noalias sret(%struct.quantum_reg_struct) align 8 %agg.result, %struct.quantum_matrix_struct* %m, i32 %width) #0 {
entry:
  %cols = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i = load i32, i32* %cols, align 4
  %cmp = icmp ne i32 %i, 1
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %cols1 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 1
  %i1 = load i32, i32* %cols1, align 4
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.44, i64 0, i64 0), i32 %i1)
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %entry
  %width2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 0
  store i32 %width, i32* %width2, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %i.0 = phi i32 [ 0, %if.end ], [ %inc8, %for.inc ]
  %size.0 = phi i32 [ 0, %if.end ], [ %size.1, %for.inc ]
  %rows = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i2 = load i32, i32* %rows, align 8
  %cmp3 = icmp slt i32 %i.0, %i2
  br i1 %cmp3, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i3 = load { float, float }*, { float, float }** %t, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds { float, float }, { float, float }* %i3, i64 %idxprom
  %arrayidx.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 0
  %arrayidx.real = load float, float* %arrayidx.realp, align 4
  %arrayidx.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx, i32 0, i32 1
  %arrayidx.imag = load float, float* %arrayidx.imagp, align 4
  %tobool = fcmp une float %arrayidx.real, 0.000000e+00
  %tobool4 = fcmp une float %arrayidx.imag, 0.000000e+00
  %tobool5 = or i1 %tobool, %tobool4
  br i1 %tobool5, label %if.then6, label %if.end7

if.then6:                                         ; preds = %for.body
  %inc = add nsw i32 %size.0, 1
  br label %if.end7

if.end7:                                          ; preds = %if.then6, %for.body
  %size.1 = phi i32 [ %inc, %if.then6 ], [ %size.0, %for.body ]
  br label %for.inc

for.inc:                                          ; preds = %if.end7
  %inc8 = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %size9 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  store i32 %size.0, i32* %size9, align 4
  %add = add nsw i32 %width, 2
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  store i32 %add, i32* %hashw, align 8
  %conv = sext i32 %size.0 to i64
  %call10 = call noalias i8* @calloc(i64 %conv, i64 16) #9
  %i4 = bitcast i8* %call10 to %struct.quantum_reg_node_struct*
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i4, %struct.quantum_reg_node_struct** %node, align 8
  %node11 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i5 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node11, align 8
  %tobool12 = icmp ne %struct.quantum_reg_node_struct* %i5, null
  br i1 %tobool12, label %if.end15, label %if.then13

if.then13:                                        ; preds = %for.end
  %call14 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.1.45, i64 0, i64 0), i32 %size.0)
  call void @exit(i32 1) #10
  unreachable

if.end15:                                         ; preds = %for.end
  %conv16 = sext i32 %size.0 to i64
  %mul = mul i64 %conv16, 16
  %call17 = call i64 @quantum_memman(i64 %mul)
  %hashw18 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i6 = load i32, i32* %hashw18, align 8
  %shl = shl i32 1, %i6
  %conv19 = sext i32 %shl to i64
  %call20 = call noalias i8* @calloc(i64 %conv19, i64 4) #9
  %i7 = bitcast i8* %call20 to i32*
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  store i32* %i7, i32** %hash, align 8
  %hash21 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  %i8 = load i32*, i32** %hash21, align 8
  %tobool22 = icmp ne i32* %i8, null
  br i1 %tobool22, label %if.end27, label %if.then23

if.then23:                                        ; preds = %if.end15
  %hashw24 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i9 = load i32, i32* %hashw24, align 8
  %shl25 = shl i32 1, %i9
  %call26 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.2.46, i64 0, i64 0), i32 %shl25)
  call void @exit(i32 1) #10
  unreachable

if.end27:                                         ; preds = %if.end15
  %hashw28 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i10 = load i32, i32* %hashw28, align 8
  %shl29 = shl i32 1, %i10
  %conv30 = sext i32 %shl29 to i64
  %mul31 = mul i64 %conv30, 4
  %call32 = call i64 @quantum_memman(i64 %mul31)
  br label %for.cond33

for.cond33:                                       ; preds = %for.inc57, %if.end27
  %i.1 = phi i32 [ 0, %if.end27 ], [ %inc58, %for.inc57 ]
  %j.0 = phi i32 [ 0, %if.end27 ], [ %j.1, %for.inc57 ]
  %rows34 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 0
  %i11 = load i32, i32* %rows34, align 8
  %cmp35 = icmp slt i32 %i.1, %i11
  br i1 %cmp35, label %for.body37, label %for.end59

for.body37:                                       ; preds = %for.cond33
  %t38 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i12 = load { float, float }*, { float, float }** %t38, align 8
  %idxprom39 = sext i32 %i.1 to i64
  %arrayidx40 = getelementptr inbounds { float, float }, { float, float }* %i12, i64 %idxprom39
  %arrayidx40.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx40, i32 0, i32 0
  %arrayidx40.real = load float, float* %arrayidx40.realp, align 4
  %arrayidx40.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx40, i32 0, i32 1
  %arrayidx40.imag = load float, float* %arrayidx40.imagp, align 4
  %tobool41 = fcmp une float %arrayidx40.real, 0.000000e+00
  %tobool42 = fcmp une float %arrayidx40.imag, 0.000000e+00
  %tobool43 = or i1 %tobool41, %tobool42
  br i1 %tobool43, label %if.then44, label %if.end56

if.then44:                                        ; preds = %for.body37
  %conv45 = sext i32 %i.1 to i64
  %node46 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i13 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node46, align 8
  %idxprom47 = sext i32 %j.0 to i64
  %arrayidx48 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i13, i64 %idxprom47
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx48, i32 0, i32 1
  store i64 %conv45, i64* %state, align 8
  %t49 = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %m, i32 0, i32 2
  %i14 = load { float, float }*, { float, float }** %t49, align 8
  %idxprom50 = sext i32 %i.1 to i64
  %arrayidx51 = getelementptr inbounds { float, float }, { float, float }* %i14, i64 %idxprom50
  %arrayidx51.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx51, i32 0, i32 0
  %arrayidx51.real = load float, float* %arrayidx51.realp, align 4
  %arrayidx51.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx51, i32 0, i32 1
  %arrayidx51.imag = load float, float* %arrayidx51.imagp, align 4
  %node52 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i15 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node52, align 8
  %idxprom53 = sext i32 %j.0 to i64
  %arrayidx54 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i15, i64 %idxprom53
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx54, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float %arrayidx51.real, float* %amplitude.realp, align 8
  store float %arrayidx51.imag, float* %amplitude.imagp, align 4
  %inc55 = add nsw i32 %j.0, 1
  br label %if.end56

if.end56:                                         ; preds = %if.then44, %for.body37
  %j.1 = phi i32 [ %inc55, %if.then44 ], [ %j.0, %for.body37 ]
  br label %for.inc57

for.inc57:                                        ; preds = %if.end56
  %inc58 = add nsw i32 %i.1, 1
  br label %for.cond33

for.end59:                                        ; preds = %for.cond33
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_new_qureg(%struct.quantum_reg_struct* noalias sret(%struct.quantum_reg_struct) align 8 %agg.result, i64 %initval, i32 %width) #0 {
entry:
  %width1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 0
  store i32 %width, i32* %width1, align 8
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  store i32 1, i32* %size, align 4
  %add = add nsw i32 %width, 2
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  store i32 %add, i32* %hashw, align 8
  %call = call noalias i8* @calloc(i64 1, i64 16) #9
  %i = bitcast i8* %call to %struct.quantum_reg_node_struct*
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i, %struct.quantum_reg_node_struct** %node, align 8
  %node2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node2, align 8
  %tobool = icmp ne %struct.quantum_reg_node_struct* %i1, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %call3 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.1.45, i64 0, i64 0), i32 1)
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %entry
  %call4 = call i64 @quantum_memman(i64 16)
  %hashw5 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i2 = load i32, i32* %hashw5, align 8
  %shl = shl i32 1, %i2
  %conv = sext i32 %shl to i64
  %call6 = call noalias i8* @calloc(i64 %conv, i64 4) #9
  %i3 = bitcast i8* %call6 to i32*
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  store i32* %i3, i32** %hash, align 8
  %hash7 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  %i4 = load i32*, i32** %hash7, align 8
  %tobool8 = icmp ne i32* %i4, null
  br i1 %tobool8, label %if.end13, label %if.then9

if.then9:                                         ; preds = %if.end
  %hashw10 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i5 = load i32, i32* %hashw10, align 8
  %shl11 = shl i32 1, %i5
  %call12 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.2.46, i64 0, i64 0), i32 %shl11)
  call void @exit(i32 1) #10
  unreachable

if.end13:                                         ; preds = %if.end
  %hashw14 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i6 = load i32, i32* %hashw14, align 8
  %shl15 = shl i32 1, %i6
  %conv16 = sext i32 %shl15 to i64
  %mul = mul i64 %conv16, 4
  %call17 = call i64 @quantum_memman(i64 %mul)
  %node18 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i7 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node18, align 8
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i7, i64 0
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  store i64 %initval, i64* %state, align 8
  %node19 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node19, align 8
  %arrayidx20 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i8, i64 0
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx20, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  store float 1.000000e+00, float* %amplitude.realp, align 8
  store float 0.000000e+00, float* %amplitude.imagp, align 4
  %call21 = call i8* @getenv(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.3.49, i64 0, i64 0)) #9
  %tobool22 = icmp ne i8* %call21, null
  br i1 %tobool22, label %if.then23, label %if.end25

if.then23:                                        ; preds = %if.end13
  call void (...) bitcast (void ()* @quantum_objcode_start to void (...)*)()
  call void @quantum_objcode_file(i8* %call21)
  %call24 = call i32 @atexit(void ()* bitcast (void (i8*)* @quantum_objcode_exit to void ()*)) #9
  br label %if.end25

if.end25:                                         ; preds = %if.then23, %if.end13
  %call26 = call i32 (i8, ...) @quantum_objcode_put(i8 zeroext 0, i64 %initval)
  ret void
}

; Function Attrs: nounwind
declare dso_local i8* @getenv(i8*) #3

; Function Attrs: nounwind
declare dso_local i32 @atexit(void ()*) #3

; Function Attrs: noinline nounwind uwtable
define dso_local { i64, { float, float }* } @quantum_qureg2matrix(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #0 {
entry:
  %retval = alloca %struct.quantum_matrix_struct, align 8
  %tmp = alloca %struct.quantum_matrix_struct, align 8
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i = load i32, i32* %width, align 8
  %shl = shl i32 1, %i
  %call = call { i64, { float, float }* } @quantum_new_matrix(i32 1, i32 %shl)
  %i1 = bitcast %struct.quantum_matrix_struct* %tmp to { i64, { float, float }* }*
  %i2 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i1, i32 0, i32 0
  %i3 = extractvalue { i64, { float, float }* } %call, 0
  store i64 %i3, i64* %i2, align 8
  %i4 = getelementptr inbounds { i64, { float, float }* }, { i64, { float, float }* }* %i1, i32 0, i32 1
  %i5 = extractvalue { i64, { float, float }* } %call, 1
  store { float, float }* %i5, { float, float }** %i4, align 8
  %i6 = bitcast %struct.quantum_matrix_struct* %retval to i8*
  %i7 = bitcast %struct.quantum_matrix_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i6, i8* align 8 %i7, i64 16, i1 false)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i8 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i8
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i9 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i9, i64 %idxprom
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %t = getelementptr inbounds %struct.quantum_matrix_struct, %struct.quantum_matrix_struct* %retval, i32 0, i32 2
  %i10 = load { float, float }*, { float, float }** %t, align 8
  %node1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i11 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node1, align 8
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i11, i64 %idxprom2
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx3, i32 0, i32 1
  %i12 = load i64, i64* %state, align 8
  %arrayidx4 = getelementptr inbounds { float, float }, { float, float }* %i10, i64 %i12
  %arrayidx4.realp = getelementptr inbounds { float, float }, { float, float }* %arrayidx4, i32 0, i32 0
  %arrayidx4.imagp = getelementptr inbounds { float, float }, { float, float }* %arrayidx4, i32 0, i32 1
  store float %amplitude.real, float* %arrayidx4.realp, align 4
  store float %amplitude.imag, float* %arrayidx4.imagp, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %i13 = bitcast %struct.quantum_matrix_struct* %retval to { i64, { float, float }* }*
  %i14 = load { i64, { float, float }* }, { i64, { float, float }* }* %i13, align 8
  ret { i64, { float, float }* } %i14
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_destroy_hash(%struct.quantum_reg_struct* %reg) #0 {
entry:
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i = load i32*, i32** %hash, align 8
  %i1 = bitcast i32* %i to i8*
  call void @free(i8* %i1) #9
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i2 = load i32, i32* %hashw, align 8
  %shl = shl i32 1, %i2
  %sub = sub nsw i32 0, %shl
  %conv = sext i32 %sub to i64
  %mul = mul i64 %conv, 4
  %call = call i64 @quantum_memman(i64 %mul)
  %hash1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  store i32* null, i32** %hash1, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_delete_qureg(%struct.quantum_reg_struct* %reg) #0 {
entry:
  call void @quantum_destroy_hash(%struct.quantum_reg_struct* %reg)
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %i1 = bitcast %struct.quantum_reg_node_struct* %i to i8*
  call void @free(i8* %i1) #9
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i2 = load i32, i32* %size, align 4
  %sub = sub nsw i32 0, %i2
  %conv = sext i32 %sub to i64
  %mul = mul i64 %conv, 16
  %call = call i64 @quantum_memman(i64 %mul)
  %node1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  store %struct.quantum_reg_node_struct* null, %struct.quantum_reg_node_struct** %node1, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_delete_qureg_hashpreserve(%struct.quantum_reg_struct* %reg) #0 {
entry:
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %i1 = bitcast %struct.quantum_reg_node_struct* %i to i8*
  call void @free(i8* %i1) #9
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i2 = load i32, i32* %size, align 4
  %sub = sub nsw i32 0, %i2
  %conv = sext i32 %sub to i64
  %mul = mul i64 %conv, 16
  %call = call i64 @quantum_memman(i64 %mul)
  %node1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  store %struct.quantum_reg_node_struct* null, %struct.quantum_reg_node_struct** %node1, align 8
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_print_qureg(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %coerce5 = alloca { float, float }, align 4
  %coerce15 = alloca { float, float }, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc34, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc34 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end35

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %amplitude.real, float* %coerce.realp, align 4
  store float %amplitude.imag, float* %coerce.imagp, align 4
  %i2 = bitcast { float, float }* %coerce to <2 x float>*
  %i3 = load <2 x float>, <2 x float>* %i2, align 4
  %call = call float @quantum_real.52(<2 x float> %i3)
  %conv = fpext float %call to double
  %node1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i4 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node1, align 8
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i4, i64 %idxprom2
  %amplitude4 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx3, i32 0, i32 0
  %amplitude4.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude4, i32 0, i32 0
  %amplitude4.real = load float, float* %amplitude4.realp, align 8
  %amplitude4.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude4, i32 0, i32 1
  %amplitude4.imag = load float, float* %amplitude4.imagp, align 4
  %coerce5.realp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 0
  %coerce5.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 1
  store float %amplitude4.real, float* %coerce5.realp, align 4
  store float %amplitude4.imag, float* %coerce5.imagp, align 4
  %i5 = bitcast { float, float }* %coerce5 to <2 x float>*
  %i6 = load <2 x float>, <2 x float>* %i5, align 4
  %call6 = call float @quantum_imag.53(<2 x float> %i6)
  %conv7 = fpext float %call6 to double
  %node8 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i7 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node8, align 8
  %idxprom9 = sext i32 %i.0 to i64
  %arrayidx10 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i7, i64 %idxprom9
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx10, i32 0, i32 1
  %i8 = load i64, i64* %state, align 8
  %node11 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i9 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node11, align 8
  %idxprom12 = sext i32 %i.0 to i64
  %arrayidx13 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i9, i64 %idxprom12
  %amplitude14 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx13, i32 0, i32 0
  %amplitude14.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude14, i32 0, i32 0
  %amplitude14.real = load float, float* %amplitude14.realp, align 8
  %amplitude14.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude14, i32 0, i32 1
  %amplitude14.imag = load float, float* %amplitude14.imagp, align 4
  %coerce15.realp = getelementptr inbounds { float, float }, { float, float }* %coerce15, i32 0, i32 0
  %coerce15.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce15, i32 0, i32 1
  store float %amplitude14.real, float* %coerce15.realp, align 4
  store float %amplitude14.imag, float* %coerce15.imagp, align 4
  %i10 = bitcast { float, float }* %coerce15 to <2 x float>*
  %i11 = load <2 x float>, <2 x float>* %i10, align 4
  %call16 = call float @quantum_prob_inline.54(<2 x float> %i11)
  %conv17 = fpext float %call16 to double
  %call18 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.4.55, i64 0, i64 0), double %conv, double %conv7, i64 %i8, double %conv17)
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i12 = load i32, i32* %width, align 8
  %sub = sub nsw i32 %i12, 1
  br label %for.cond19

for.cond19:                                       ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ %sub, %for.body ], [ %dec, %for.inc ]
  %cmp20 = icmp sge i32 %j.0, 0
  br i1 %cmp20, label %for.body22, label %for.end

for.body22:                                       ; preds = %for.cond19
  %rem = srem i32 %j.0, 4
  %cmp23 = icmp eq i32 %rem, 3
  br i1 %cmp23, label %if.then, label %if.end

if.then:                                          ; preds = %for.body22
  %call25 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.5.56, i64 0, i64 0))
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body22
  %sh_prom = zext i32 %j.0 to i64
  %shl = shl i64 1, %sh_prom
  %node26 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i13 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node26, align 8
  %idxprom27 = sext i32 %i.0 to i64
  %arrayidx28 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i13, i64 %idxprom27
  %state29 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx28, i32 0, i32 1
  %i14 = load i64, i64* %state29, align 8
  %and = and i64 %shl, %i14
  %cmp30 = icmp ugt i64 %and, 0
  %conv31 = zext i1 %cmp30 to i32
  %call32 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.6.57, i64 0, i64 0), i32 %conv31)
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %dec = add nsw i32 %j.0, -1
  br label %for.cond19

for.end:                                          ; preds = %for.cond19
  %call33 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.7.58, i64 0, i64 0))
  br label %for.inc34

for.inc34:                                        ; preds = %for.end
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end35:                                        ; preds = %for.cond
  %call36 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.8, i64 0, i64 0))
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_real.52(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 0
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_imag.53(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %i1 = bitcast { float, float }* %a to float*
  %arrayidx = getelementptr inbounds float, float* %i1, i64 1
  %i2 = load float, float* %arrayidx, align 4
  ret float %i2
}

; Function Attrs: noinline nounwind uwtable
define internal float @quantum_prob_inline.54(<2 x float> %a.coerce) #2 {
entry:
  %a = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce5 = alloca { float, float }, align 4
  %i = bitcast { float, float }* %a to <2 x float>*
  store <2 x float> %a.coerce, <2 x float>* %i, align 4
  %a.realp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real = load float, float* %a.realp, align 4
  %a.imagp = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag = load float, float* %a.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %a.real, float* %coerce.realp, align 4
  store float %a.imag, float* %coerce.imagp, align 4
  %i1 = bitcast { float, float }* %coerce to <2 x float>*
  %i2 = load <2 x float>, <2 x float>* %i1, align 4
  %call = call float @quantum_real.52(<2 x float> %i2)
  %a.realp1 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 0
  %a.real2 = load float, float* %a.realp1, align 4
  %a.imagp3 = getelementptr inbounds { float, float }, { float, float }* %a, i32 0, i32 1
  %a.imag4 = load float, float* %a.imagp3, align 4
  %coerce5.realp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 0
  %coerce5.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce5, i32 0, i32 1
  store float %a.real2, float* %coerce5.realp, align 4
  store float %a.imag4, float* %coerce5.imagp, align 4
  %i3 = bitcast { float, float }* %coerce5 to <2 x float>*
  %i4 = load <2 x float>, <2 x float>* %i3, align 4
  %call6 = call float @quantum_imag.53(<2 x float> %i4)
  %mul = fmul float %call, %call
  %mul7 = fmul float %call6, %call6
  %add = fadd float %mul, %mul7
  ret float %add
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_print_expn(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i2 = load i64, i64* %state, align 8
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i3 = load i32, i32* %width, align 8
  %div = sdiv i32 %i3, 2
  %shl = shl i32 1, %div
  %mul = mul nsw i32 %i.0, %shl
  %conv = sext i32 %mul to i64
  %sub = sub i64 %i2, %conv
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.9, i64 0, i64 0), i32 %i.0, i64 %sub)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_addscratch(i32 %bits, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i = load i32, i32* %width, align 8
  %width1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i1 = load i32, i32* %width1, align 8
  %add = add nsw i32 %i1, %bits
  store i32 %add, i32* %width1, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i2 = load i32, i32* %size, align 4
  %cmp = icmp slt i32 %i.0, %i2
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i4 = load i64, i64* %state, align 8
  %sh_prom = zext i32 %bits to i64
  %shl = shl i64 %i4, %sh_prom
  %node2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i5 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node2, align 8
  %idxprom3 = sext i32 %i.0 to i64
  %arrayidx4 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i5, i64 %idxprom3
  %state5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx4, i32 0, i32 1
  store i64 %shl, i64* %state5, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_print_hash(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i = load i32, i32* %hashw, align 8
  %shl = shl i32 1, %i
  %cmp = icmp slt i32 %i.0, %shl
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %tobool = icmp ne i32 %i.0, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i1 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %idxprom
  %i2 = load i32, i32* %arrayidx, align 4
  %sub = sub nsw i32 %i2, 1
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %hash1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i4 = load i32*, i32** %hash1, align 8
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds i32, i32* %i4, i64 %idxprom2
  %i5 = load i32, i32* %arrayidx3, align 4
  %sub4 = sub nsw i32 %i5, 1
  %idxprom5 = sext i32 %sub4 to i64
  %arrayidx6 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom5
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx6, i32 0, i32 1
  %i6 = load i64, i64* %state, align 8
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.10, i64 0, i64 0), i32 %i.0, i32 %sub, i64 %i6)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_kronecker(%struct.quantum_reg_struct* noalias sret(%struct.quantum_reg_struct) align 8 %agg.result, %struct.quantum_reg_struct* %reg1, %struct.quantum_reg_struct* %reg2) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 0
  %i = load i32, i32* %width, align 8
  %width1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 0
  %i1 = load i32, i32* %width1, align 8
  %add = add nsw i32 %i, %i1
  %width2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 0
  store i32 %add, i32* %width2, align 8
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 1
  %i2 = load i32, i32* %size, align 4
  %size3 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 1
  %i3 = load i32, i32* %size3, align 4
  %mul = mul nsw i32 %i2, %i3
  %size4 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  store i32 %mul, i32* %size4, align 4
  %size5 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 1
  %i4 = load i32, i32* %size5, align 4
  %size6 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 1
  %i5 = load i32, i32* %size6, align 4
  %mul7 = mul nsw i32 %i4, %i5
  %add8 = add nsw i32 %mul7, 2
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  store i32 %add8, i32* %hashw, align 8
  %size9 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  %i6 = load i32, i32* %size9, align 4
  %conv = sext i32 %i6 to i64
  %call = call noalias i8* @calloc(i64 %conv, i64 16) #9
  %i7 = bitcast i8* %call to %struct.quantum_reg_node_struct*
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i7, %struct.quantum_reg_node_struct** %node, align 8
  %node10 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node10, align 8
  %tobool = icmp ne %struct.quantum_reg_node_struct* %i8, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %size11 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  %i9 = load i32, i32* %size11, align 4
  %call12 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.1.45, i64 0, i64 0), i32 %i9)
  call void @exit(i32 1) #10
  unreachable

if.end:                                           ; preds = %entry
  %size13 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  %i10 = load i32, i32* %size13, align 4
  %conv14 = sext i32 %i10 to i64
  %mul15 = mul i64 %conv14, 16
  %call16 = call i64 @quantum_memman(i64 %mul15)
  %hashw17 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i11 = load i32, i32* %hashw17, align 8
  %shl = shl i32 1, %i11
  %conv18 = sext i32 %shl to i64
  %call19 = call noalias i8* @calloc(i64 %conv18, i64 4) #9
  %i12 = bitcast i8* %call19 to i32*
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  store i32* %i12, i32** %hash, align 8
  %hash20 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  %i13 = load i32*, i32** %hash20, align 8
  %tobool21 = icmp ne i32* %i13, null
  br i1 %tobool21, label %if.end26, label %if.then22

if.then22:                                        ; preds = %if.end
  %hashw23 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i14 = load i32, i32* %hashw23, align 8
  %shl24 = shl i32 1, %i14
  %call25 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.2.46, i64 0, i64 0), i32 %shl24)
  call void @exit(i32 1) #10
  unreachable

if.end26:                                         ; preds = %if.end
  %hashw27 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  %i15 = load i32, i32* %hashw27, align 8
  %shl28 = shl i32 1, %i15
  %conv29 = sext i32 %shl28 to i64
  %mul30 = mul i64 %conv29, 4
  %call31 = call i64 @quantum_memman(i64 %mul30)
  br label %for.cond

for.cond:                                         ; preds = %for.inc69, %if.end26
  %i.0 = phi i32 [ 0, %if.end26 ], [ %inc70, %for.inc69 ]
  %size32 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 1
  %i16 = load i32, i32* %size32, align 4
  %cmp = icmp slt i32 %i.0, %i16
  br i1 %cmp, label %for.body, label %for.end71

for.body:                                         ; preds = %for.cond
  br label %for.cond34

for.cond34:                                       ; preds = %for.inc, %for.body
  %j.0 = phi i32 [ 0, %for.body ], [ %inc, %for.inc ]
  %size35 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 1
  %i17 = load i32, i32* %size35, align 4
  %cmp36 = icmp slt i32 %j.0, %i17
  br i1 %cmp36, label %for.body38, label %for.end

for.body38:                                       ; preds = %for.cond34
  %node39 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 3
  %i18 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node39, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i18, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i19 = load i64, i64* %state, align 8
  %width40 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 0
  %i20 = load i32, i32* %width40, align 8
  %sh_prom = zext i32 %i20 to i64
  %shl41 = shl i64 %i19, %sh_prom
  %node42 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 3
  %i21 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node42, align 8
  %idxprom43 = sext i32 %j.0 to i64
  %arrayidx44 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i21, i64 %idxprom43
  %state45 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx44, i32 0, i32 1
  %i22 = load i64, i64* %state45, align 8
  %or = or i64 %shl41, %i22
  %node46 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i23 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node46, align 8
  %size47 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 1
  %i24 = load i32, i32* %size47, align 4
  %mul48 = mul nsw i32 %i.0, %i24
  %add49 = add nsw i32 %mul48, %j.0
  %idxprom50 = sext i32 %add49 to i64
  %arrayidx51 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i23, i64 %idxprom50
  %state52 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx51, i32 0, i32 1
  store i64 %or, i64* %state52, align 8
  %node53 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 3
  %i25 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node53, align 8
  %idxprom54 = sext i32 %i.0 to i64
  %arrayidx55 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i25, i64 %idxprom54
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx55, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %node56 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 3
  %i26 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node56, align 8
  %idxprom57 = sext i32 %j.0 to i64
  %arrayidx58 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i26, i64 %idxprom57
  %amplitude59 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx58, i32 0, i32 0
  %amplitude59.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude59, i32 0, i32 0
  %amplitude59.real = load float, float* %amplitude59.realp, align 8
  %amplitude59.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude59, i32 0, i32 1
  %amplitude59.imag = load float, float* %amplitude59.imagp, align 4
  %mul_ac = fmul float %amplitude.real, %amplitude59.real
  %mul_bd = fmul float %amplitude.imag, %amplitude59.imag
  %mul_ad = fmul float %amplitude.real, %amplitude59.imag
  %mul_bc = fmul float %amplitude.imag, %amplitude59.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %for.body38
  %isnan_cmp60 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp60, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call61 = call <2 x float> @__mulsc3(float %amplitude.real, float %amplitude.imag, float %amplitude59.real, float %amplitude59.imag) #9
  %i27 = bitcast { float, float }* %coerce to <2 x float>*
  store <2 x float> %call61, <2 x float>* %i27, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.real = load float, float* %coerce.realp, align 4
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  %coerce.imag = load float, float* %coerce.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %for.body38
  %real_mul_phi = phi float [ %mul_r, %for.body38 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %for.body38 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce.imag, %complex_mul_libcall ]
  %node62 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i28 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node62, align 8
  %size63 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 1
  %i29 = load i32, i32* %size63, align 4
  %mul64 = mul nsw i32 %i.0, %i29
  %add65 = add nsw i32 %mul64, %j.0
  %idxprom66 = sext i32 %add65 to i64
  %arrayidx67 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i28, i64 %idxprom66
  %amplitude68 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx67, i32 0, i32 0
  %amplitude68.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude68, i32 0, i32 0
  %amplitude68.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude68, i32 0, i32 1
  store float %real_mul_phi, float* %amplitude68.realp, align 8
  store float %imag_mul_phi, float* %amplitude68.imagp, align 4
  br label %for.inc

for.inc:                                          ; preds = %complex_mul_cont
  %inc = add nsw i32 %j.0, 1
  br label %for.cond34

for.end:                                          ; preds = %for.cond34
  br label %for.inc69

for.inc69:                                        ; preds = %for.end
  %inc70 = add nsw i32 %i.0, 1
  br label %for.cond

for.end71:                                        ; preds = %for.cond
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @quantum_state_collapse(%struct.quantum_reg_struct* noalias sret(%struct.quantum_reg_struct) align 8 %agg.result, i32 %pos, i32 %value, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #2 {
entry:
  %coerce = alloca { float, float }, align 4
  %coerce91 = alloca { float, float }, align 4
  %sh_prom = zext i32 %pos to i64
  %shl = shl i64 1, %sh_prom
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %d.0 = phi double [ 0.000000e+00, %entry ], [ %d.1, %for.inc ]
  %size.0 = phi i32 [ 0, %entry ], [ %size.1, %for.inc ]
  %i.0 = phi i32 [ 0, %entry ], [ %inc14, %for.inc ]
  %size1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i = load i32, i32* %size1, align 4
  %cmp = icmp slt i32 %i.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i1 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i1, i64 %idxprom
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx, i32 0, i32 1
  %i2 = load i64, i64* %state, align 8
  %and = and i64 %i2, %shl
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %land.lhs.true, label %lor.lhs.false

land.lhs.true:                                    ; preds = %for.body
  %tobool2 = icmp ne i32 %value, 0
  br i1 %tobool2, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %land.lhs.true, %for.body
  %node3 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node3, align 8
  %idxprom4 = sext i32 %i.0 to i64
  %arrayidx5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom4
  %state6 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx5, i32 0, i32 1
  %i4 = load i64, i64* %state6, align 8
  %and7 = and i64 %i4, %shl
  %tobool8 = icmp ne i64 %and7, 0
  br i1 %tobool8, label %if.end, label %land.lhs.true9

land.lhs.true9:                                   ; preds = %lor.lhs.false
  %tobool10 = icmp ne i32 %value, 0
  br i1 %tobool10, label %if.end, label %if.then

if.then:                                          ; preds = %land.lhs.true9, %land.lhs.true
  %node11 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i5 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node11, align 8
  %idxprom12 = sext i32 %i.0 to i64
  %arrayidx13 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i5, i64 %idxprom12
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx13, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %amplitude.real, float* %coerce.realp, align 4
  store float %amplitude.imag, float* %coerce.imagp, align 4
  %i6 = bitcast { float, float }* %coerce to <2 x float>*
  %i7 = load <2 x float>, <2 x float>* %i6, align 4
  %call = call float @quantum_prob_inline.54(<2 x float> %i7)
  %conv = fpext float %call to double
  %add = fadd double %d.0, %conv
  %inc = add nsw i32 %size.0, 1
  br label %if.end

if.end:                                           ; preds = %if.then, %land.lhs.true9, %lor.lhs.false
  %d.1 = phi double [ %add, %if.then ], [ %d.0, %lor.lhs.false ], [ %d.0, %land.lhs.true9 ]
  %size.1 = phi i32 [ %inc, %if.then ], [ %size.0, %lor.lhs.false ], [ %size.0, %land.lhs.true9 ]
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %inc14 = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %width = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 0
  %i8 = load i32, i32* %width, align 8
  %sub = sub nsw i32 %i8, 1
  %width15 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 0
  store i32 %sub, i32* %width15, align 8
  %size16 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 1
  store i32 %size.0, i32* %size16, align 4
  %conv17 = sext i32 %size.0 to i64
  %call18 = call noalias i8* @calloc(i64 %conv17, i64 16) #9
  %i9 = bitcast i8* %call18 to %struct.quantum_reg_node_struct*
  %node19 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  store %struct.quantum_reg_node_struct* %i9, %struct.quantum_reg_node_struct** %node19, align 8
  %node20 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i10 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node20, align 8
  %tobool21 = icmp ne %struct.quantum_reg_node_struct* %i10, null
  br i1 %tobool21, label %if.end24, label %if.then22

if.then22:                                        ; preds = %for.end
  %call23 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.11, i64 0, i64 0), i32 %size.0)
  call void @exit(i32 1) #10
  unreachable

if.end24:                                         ; preds = %for.end
  %conv25 = sext i32 %size.0 to i64
  %mul = mul i64 %conv25, 16
  %call26 = call i64 @quantum_memman(i64 %mul)
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i11 = load i32, i32* %hashw, align 8
  %hashw27 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 2
  store i32 %i11, i32* %hashw27, align 8
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i12 = load i32*, i32** %hash, align 8
  %hash28 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 4
  store i32* %i12, i32** %hash28, align 8
  br label %for.cond29

for.cond29:                                       ; preds = %for.inc100, %if.end24
  %j.0 = phi i32 [ 0, %if.end24 ], [ %j.1, %for.inc100 ]
  %i.1 = phi i32 [ 0, %if.end24 ], [ %inc101, %for.inc100 ]
  %size30 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 1
  %i13 = load i32, i32* %size30, align 4
  %cmp31 = icmp slt i32 %i.1, %i13
  br i1 %cmp31, label %for.body33, label %for.end102

for.body33:                                       ; preds = %for.cond29
  %node34 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i14 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node34, align 8
  %idxprom35 = sext i32 %i.1 to i64
  %arrayidx36 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i14, i64 %idxprom35
  %state37 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx36, i32 0, i32 1
  %i15 = load i64, i64* %state37, align 8
  %and38 = and i64 %i15, %shl
  %tobool39 = icmp ne i64 %and38, 0
  br i1 %tobool39, label %land.lhs.true40, label %lor.lhs.false42

land.lhs.true40:                                  ; preds = %for.body33
  %tobool41 = icmp ne i32 %value, 0
  br i1 %tobool41, label %if.then51, label %lor.lhs.false42

lor.lhs.false42:                                  ; preds = %land.lhs.true40, %for.body33
  %node43 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i16 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node43, align 8
  %idxprom44 = sext i32 %i.1 to i64
  %arrayidx45 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i16, i64 %idxprom44
  %state46 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx45, i32 0, i32 1
  %i17 = load i64, i64* %state46, align 8
  %and47 = and i64 %i17, %shl
  %tobool48 = icmp ne i64 %and47, 0
  br i1 %tobool48, label %if.end99, label %land.lhs.true49

land.lhs.true49:                                  ; preds = %lor.lhs.false42
  %tobool50 = icmp ne i32 %value, 0
  br i1 %tobool50, label %if.end99, label %if.then51

if.then51:                                        ; preds = %land.lhs.true49, %land.lhs.true40
  br label %for.cond52

for.cond52:                                       ; preds = %for.inc59, %if.then51
  %k.0 = phi i32 [ 0, %if.then51 ], [ %inc60, %for.inc59 ]
  %rpat.0 = phi i64 [ 0, %if.then51 ], [ %add58, %for.inc59 ]
  %cmp53 = icmp slt i32 %k.0, %pos
  br i1 %cmp53, label %for.body55, label %for.end61

for.body55:                                       ; preds = %for.cond52
  %sh_prom56 = zext i32 %k.0 to i64
  %shl57 = shl i64 1, %sh_prom56
  %add58 = add i64 %rpat.0, %shl57
  br label %for.inc59

for.inc59:                                        ; preds = %for.body55
  %inc60 = add nsw i32 %k.0, 1
  br label %for.cond52

for.end61:                                        ; preds = %for.cond52
  %node62 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i18 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node62, align 8
  %idxprom63 = sext i32 %i.1 to i64
  %arrayidx64 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i18, i64 %idxprom63
  %state65 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx64, i32 0, i32 1
  %i19 = load i64, i64* %state65, align 8
  %and66 = and i64 %rpat.0, %i19
  br label %for.cond67

for.cond67:                                       ; preds = %for.inc74, %for.end61
  %k.1 = phi i32 [ 63, %for.end61 ], [ %dec, %for.inc74 ]
  %lpat.0 = phi i64 [ 0, %for.end61 ], [ %add73, %for.inc74 ]
  %cmp68 = icmp sgt i32 %k.1, %pos
  br i1 %cmp68, label %for.body70, label %for.end75

for.body70:                                       ; preds = %for.cond67
  %sh_prom71 = zext i32 %k.1 to i64
  %shl72 = shl i64 1, %sh_prom71
  %add73 = add i64 %lpat.0, %shl72
  br label %for.inc74

for.inc74:                                        ; preds = %for.body70
  %dec = add nsw i32 %k.1, -1
  br label %for.cond67

for.end75:                                        ; preds = %for.cond67
  %node76 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i20 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node76, align 8
  %idxprom77 = sext i32 %i.1 to i64
  %arrayidx78 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i20, i64 %idxprom77
  %state79 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx78, i32 0, i32 1
  %i21 = load i64, i64* %state79, align 8
  %and80 = and i64 %lpat.0, %i21
  %shr = lshr i64 %and80, 1
  %or = or i64 %shr, %and66
  %node81 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i22 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node81, align 8
  %idxprom82 = sext i32 %j.0 to i64
  %arrayidx83 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i22, i64 %idxprom82
  %state84 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx83, i32 0, i32 1
  store i64 %or, i64* %state84, align 8
  %node85 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i23 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node85, align 8
  %idxprom86 = sext i32 %i.1 to i64
  %arrayidx87 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i23, i64 %idxprom86
  %amplitude88 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx87, i32 0, i32 0
  %amplitude88.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude88, i32 0, i32 0
  %amplitude88.real = load float, float* %amplitude88.realp, align 8
  %amplitude88.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude88, i32 0, i32 1
  %amplitude88.imag = load float, float* %amplitude88.imagp, align 4
  %mul_ac = fmul float %amplitude88.real, 1.000000e+00
  %mul_bd = fmul float %amplitude88.imag, 0.000000e+00
  %mul_ad = fmul float %amplitude88.real, 0.000000e+00
  %mul_bc = fmul float %amplitude88.imag, 1.000000e+00
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %for.end75
  %isnan_cmp89 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp89, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call90 = call <2 x float> @__mulsc3(float %amplitude88.real, float %amplitude88.imag, float 1.000000e+00, float 0.000000e+00) #9
  %i24 = bitcast { float, float }* %coerce91 to <2 x float>*
  store <2 x float> %call90, <2 x float>* %i24, align 4
  %coerce91.realp = getelementptr inbounds { float, float }, { float, float }* %coerce91, i32 0, i32 0
  %coerce91.real = load float, float* %coerce91.realp, align 4
  %coerce91.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce91, i32 0, i32 1
  %coerce91.imag = load float, float* %coerce91.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %for.end75
  %real_mul_phi = phi float [ %mul_r, %for.end75 ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce91.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %for.end75 ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce91.imag, %complex_mul_libcall ]
  %call92 = call double @sqrt(double %d.0) #9
  %conv93 = fptrunc double %call92 to float
  %i25 = fdiv float %real_mul_phi, %conv93
  %i26 = fdiv float %imag_mul_phi, %conv93
  %node94 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %agg.result, i32 0, i32 3
  %i27 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node94, align 8
  %idxprom95 = sext i32 %j.0 to i64
  %arrayidx96 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i27, i64 %idxprom95
  %amplitude97 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx96, i32 0, i32 0
  %amplitude97.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude97, i32 0, i32 0
  %amplitude97.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude97, i32 0, i32 1
  store float %i25, float* %amplitude97.realp, align 8
  store float %i26, float* %amplitude97.imagp, align 4
  %inc98 = add nsw i32 %j.0, 1
  br label %if.end99

if.end99:                                         ; preds = %complex_mul_cont, %land.lhs.true49, %lor.lhs.false42
  %j.1 = phi i32 [ %inc98, %complex_mul_cont ], [ %j.0, %lor.lhs.false42 ], [ %j.0, %land.lhs.true49 ]
  br label %for.inc100

for.inc100:                                       ; preds = %if.end99
  %inc101 = add nsw i32 %i.1, 1
  br label %for.cond29

for.end102:                                       ; preds = %for.cond29
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local <2 x float> @quantum_dot_product(%struct.quantum_reg_struct* %reg1, %struct.quantum_reg_struct* %reg2) #2 {
entry:
  %retval = alloca { float, float }, align 4
  %f = alloca { float, float }, align 4
  %coerce = alloca { float, float }, align 4
  %coerce22 = alloca { float, float }, align 4
  %coerce29 = alloca { float, float }, align 4
  %f.realp = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 0
  %f.imagp = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 1
  store float 0.000000e+00, float* %f.realp, align 4
  store float 0.000000e+00, float* %f.imagp, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 2
  %i = load i32, i32* %hashw, align 8
  %shl = shl i32 1, %i
  %cmp = icmp slt i32 %i.0, %shl
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 4
  %i1 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %idxprom
  store i32 0, i32* %arrayidx, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc6, %for.end
  %i.1 = phi i32 [ 0, %for.end ], [ %inc7, %for.inc6 ]
  %size = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 1
  %i2 = load i32, i32* %size, align 4
  %cmp2 = icmp slt i32 %i.1, %i2
  br i1 %cmp2, label %for.body3, label %for.end8

for.body3:                                        ; preds = %for.cond1
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %idxprom4 = sext i32 %i.1 to i64
  %arrayidx5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom4
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx5, i32 0, i32 1
  %i4 = load i64, i64* %state, align 8
  call void @quantum_add_hash.61(i64 %i4, i32 %i.1, %struct.quantum_reg_struct* %reg2)
  br label %for.inc6

for.inc6:                                         ; preds = %for.body3
  %inc7 = add nsw i32 %i.1, 1
  br label %for.cond1

for.end8:                                         ; preds = %for.cond1
  br label %for.cond9

for.cond9:                                        ; preds = %for.inc34, %for.end8
  %i.2 = phi i32 [ 0, %for.end8 ], [ %inc35, %for.inc34 ]
  %size10 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 1
  %i5 = load i32, i32* %size10, align 4
  %cmp11 = icmp slt i32 %i.2, %i5
  br i1 %cmp11, label %for.body12, label %for.end36

for.body12:                                       ; preds = %for.cond9
  %node13 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 3
  %i6 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node13, align 8
  %idxprom14 = sext i32 %i.2 to i64
  %arrayidx15 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i6, i64 %idxprom14
  %state16 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx15, i32 0, i32 1
  %i7 = load i64, i64* %state16, align 8
  %call = call i32 @quantum_get_state.62(i64 %i7, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg2)
  %cmp17 = icmp sgt i32 %call, -1
  br i1 %cmp17, label %if.then, label %if.end

if.then:                                          ; preds = %for.body12
  %node18 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg1, i32 0, i32 3
  %i8 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node18, align 8
  %idxprom19 = sext i32 %i.2 to i64
  %arrayidx20 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i8, i64 %idxprom19
  %amplitude = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx20, i32 0, i32 0
  %amplitude.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 0
  %amplitude.real = load float, float* %amplitude.realp, align 8
  %amplitude.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude, i32 0, i32 1
  %amplitude.imag = load float, float* %amplitude.imagp, align 4
  %coerce.realp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 0
  %coerce.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce, i32 0, i32 1
  store float %amplitude.real, float* %coerce.realp, align 4
  store float %amplitude.imag, float* %coerce.imagp, align 4
  %i9 = bitcast { float, float }* %coerce to <2 x float>*
  %i10 = load <2 x float>, <2 x float>* %i9, align 4
  %call21 = call <2 x float> @quantum_conj(<2 x float> %i10)
  %i11 = bitcast { float, float }* %coerce22 to <2 x float>*
  store <2 x float> %call21, <2 x float>* %i11, align 4
  %coerce22.realp = getelementptr inbounds { float, float }, { float, float }* %coerce22, i32 0, i32 0
  %coerce22.real = load float, float* %coerce22.realp, align 4
  %coerce22.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce22, i32 0, i32 1
  %coerce22.imag = load float, float* %coerce22.imagp, align 4
  %node23 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg2, i32 0, i32 3
  %i12 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node23, align 8
  %idxprom24 = sext i32 %call to i64
  %arrayidx25 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i12, i64 %idxprom24
  %amplitude26 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx25, i32 0, i32 0
  %amplitude26.realp = getelementptr inbounds { float, float }, { float, float }* %amplitude26, i32 0, i32 0
  %amplitude26.real = load float, float* %amplitude26.realp, align 8
  %amplitude26.imagp = getelementptr inbounds { float, float }, { float, float }* %amplitude26, i32 0, i32 1
  %amplitude26.imag = load float, float* %amplitude26.imagp, align 4
  %mul_ac = fmul float %coerce22.real, %amplitude26.real
  %mul_bd = fmul float %coerce22.imag, %amplitude26.imag
  %mul_ad = fmul float %coerce22.real, %amplitude26.imag
  %mul_bc = fmul float %coerce22.imag, %amplitude26.real
  %mul_r = fsub float %mul_ac, %mul_bd
  %mul_i = fadd float %mul_ad, %mul_bc
  %isnan_cmp = fcmp uno float %mul_r, %mul_r
  br i1 %isnan_cmp, label %complex_mul_imag_nan, label %complex_mul_cont, !prof !2

complex_mul_imag_nan:                             ; preds = %if.then
  %isnan_cmp27 = fcmp uno float %mul_i, %mul_i
  br i1 %isnan_cmp27, label %complex_mul_libcall, label %complex_mul_cont, !prof !2

complex_mul_libcall:                              ; preds = %complex_mul_imag_nan
  %call28 = call <2 x float> @__mulsc3(float %coerce22.real, float %coerce22.imag, float %amplitude26.real, float %amplitude26.imag) #9
  %i13 = bitcast { float, float }* %coerce29 to <2 x float>*
  store <2 x float> %call28, <2 x float>* %i13, align 4
  %coerce29.realp = getelementptr inbounds { float, float }, { float, float }* %coerce29, i32 0, i32 0
  %coerce29.real = load float, float* %coerce29.realp, align 4
  %coerce29.imagp = getelementptr inbounds { float, float }, { float, float }* %coerce29, i32 0, i32 1
  %coerce29.imag = load float, float* %coerce29.imagp, align 4
  br label %complex_mul_cont

complex_mul_cont:                                 ; preds = %complex_mul_libcall, %complex_mul_imag_nan, %if.then
  %real_mul_phi = phi float [ %mul_r, %if.then ], [ %mul_r, %complex_mul_imag_nan ], [ %coerce29.real, %complex_mul_libcall ]
  %imag_mul_phi = phi float [ %mul_i, %if.then ], [ %mul_i, %complex_mul_imag_nan ], [ %coerce29.imag, %complex_mul_libcall ]
  %f.realp30 = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 0
  %f.real = load float, float* %f.realp30, align 4
  %f.imagp31 = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 1
  %f.imag = load float, float* %f.imagp31, align 4
  %add.r = fadd float %f.real, %real_mul_phi
  %add.i = fadd float %f.imag, %imag_mul_phi
  %f.realp32 = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 0
  %f.imagp33 = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 1
  store float %add.r, float* %f.realp32, align 4
  store float %add.i, float* %f.imagp33, align 4
  br label %if.end

if.end:                                           ; preds = %complex_mul_cont, %for.body12
  br label %for.inc34

for.inc34:                                        ; preds = %if.end
  %inc35 = add nsw i32 %i.2, 1
  br label %for.cond9

for.end36:                                        ; preds = %for.cond9
  %f.realp37 = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 0
  %f.real38 = load float, float* %f.realp37, align 4
  %f.imagp39 = getelementptr inbounds { float, float }, { float, float }* %f, i32 0, i32 1
  %f.imag40 = load float, float* %f.imagp39, align 4
  %retval.realp = getelementptr inbounds { float, float }, { float, float }* %retval, i32 0, i32 0
  %retval.imagp = getelementptr inbounds { float, float }, { float, float }* %retval, i32 0, i32 1
  store float %f.real38, float* %retval.realp, align 4
  store float %f.imag40, float* %retval.imagp, align 4
  %i14 = bitcast { float, float }* %retval to <2 x float>*
  %i15 = load <2 x float>, <2 x float>* %i14, align 4
  ret <2 x float> %i15
}

; Function Attrs: noinline nounwind uwtable
define internal void @quantum_add_hash.61(i64 %a, i32 %pos, %struct.quantum_reg_struct* %reg) #0 {
entry:
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i = load i32, i32* %hashw, align 8
  %call = call i32 @quantum_hash64.63(i64 %a, i32 %i)
  br label %while.cond

while.cond:                                       ; preds = %if.end, %entry
  %i.0 = phi i32 [ %call, %entry ], [ %i.1, %if.end ]
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i1 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %idxprom
  %i2 = load i32, i32* %arrayidx, align 4
  %tobool = icmp ne i32 %i2, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %inc = add nsw i32 %i.0, 1
  %hashw1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i3 = load i32, i32* %hashw1, align 8
  %shl = shl i32 1, %i3
  %cmp = icmp eq i32 %inc, %shl
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %while.body
  br label %if.end

if.end:                                           ; preds = %if.then, %while.body
  %i.1 = phi i32 [ 0, %if.then ], [ %inc, %while.body ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %add = add nsw i32 %pos, 1
  %hash2 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i4 = load i32*, i32** %hash2, align 8
  %idxprom3 = sext i32 %i.0 to i64
  %arrayidx4 = getelementptr inbounds i32, i32* %i4, i64 %idxprom3
  store i32 %add, i32* %arrayidx4, align 4
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal i32 @quantum_get_state.62(i64 %a, %struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %reg) #0 {
entry:
  %hashw = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i = load i32, i32* %hashw, align 8
  %call = call i32 @quantum_hash64.63(i64 %a, i32 %i)
  br label %while.cond

while.cond:                                       ; preds = %if.end13, %entry
  %i.0 = phi i32 [ %call, %entry ], [ %i.1, %if.end13 ]
  %hash = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i1 = load i32*, i32** %hash, align 8
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %idxprom
  %i2 = load i32, i32* %arrayidx, align 4
  %tobool = icmp ne i32 %i2, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %node = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 3
  %i3 = load %struct.quantum_reg_node_struct*, %struct.quantum_reg_node_struct** %node, align 8
  %hash1 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i4 = load i32*, i32** %hash1, align 8
  %idxprom2 = sext i32 %i.0 to i64
  %arrayidx3 = getelementptr inbounds i32, i32* %i4, i64 %idxprom2
  %i5 = load i32, i32* %arrayidx3, align 4
  %sub = sub nsw i32 %i5, 1
  %idxprom4 = sext i32 %sub to i64
  %arrayidx5 = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %i3, i64 %idxprom4
  %state = getelementptr inbounds %struct.quantum_reg_node_struct, %struct.quantum_reg_node_struct* %arrayidx5, i32 0, i32 1
  %i6 = load i64, i64* %state, align 8
  %cmp = icmp eq i64 %i6, %a
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %while.body
  %hash6 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 4
  %i7 = load i32*, i32** %hash6, align 8
  %idxprom7 = sext i32 %i.0 to i64
  %arrayidx8 = getelementptr inbounds i32, i32* %i7, i64 %idxprom7
  %i8 = load i32, i32* %arrayidx8, align 4
  %sub9 = sub nsw i32 %i8, 1
  br label %return

if.end:                                           ; preds = %while.body
  %inc = add nsw i32 %i.0, 1
  %hashw10 = getelementptr inbounds %struct.quantum_reg_struct, %struct.quantum_reg_struct* %reg, i32 0, i32 2
  %i9 = load i32, i32* %hashw10, align 8
  %shl = shl i32 1, %i9
  %cmp11 = icmp eq i32 %inc, %shl
  br i1 %cmp11, label %if.then12, label %if.end13

if.then12:                                        ; preds = %if.end
  br label %if.end13

if.end13:                                         ; preds = %if.then12, %if.end
  %i.1 = phi i32 [ 0, %if.then12 ], [ %inc, %if.end ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  br label %return

return:                                           ; preds = %while.end, %if.then
  %retval.0 = phi i32 [ %sub9, %if.then ], [ -1, %while.end ]
  ret i32 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define internal i32 @quantum_hash64.63(i64 %key, i32 %width) #0 {
entry:
  %and = and i64 %key, 4294967295
  %shr = lshr i64 %key, 32
  %xor = xor i64 %and, %shr
  %conv = trunc i64 %xor to i32
  %conv1 = zext i32 %conv to i64
  %mul = mul i64 %conv1, 2654404609
  %conv2 = trunc i64 %mul to i32
  %sub = sub nsw i32 32, %width
  %shr3 = lshr i32 %conv2, %sub
  ret i32 %shr3
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main(i32 %argc, i8** %argv) #0 {
entry:
  %qr = alloca %struct.quantum_reg_struct, align 8
  %c = alloca i32, align 4
  %q = alloca i32, align 4
  %tmp = alloca %struct.quantum_reg_struct, align 8
  call void @spec_srand(i32 26)
  %cmp = icmp eq i32 %argc, 1
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.64, i64 0, i64 0))
  br label %return

if.end:                                           ; preds = %entry
  %arrayidx = getelementptr inbounds i8*, i8** %argv, i64 1
  %i = load i8*, i8** %arrayidx, align 8
  %call1 = call i32 @atoi(i8* %i) #11
  %cmp2 = icmp slt i32 %call1, 15
  br i1 %cmp2, label %if.then3, label %if.end5

if.then3:                                         ; preds = %if.end
  %call4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.1.65, i64 0, i64 0))
  br label %return

if.end5:                                          ; preds = %if.end
  %mul = mul nsw i32 %call1, %call1
  %call6 = call i32 @quantum_getwidth(i32 %mul)
  %call7 = call i32 @quantum_getwidth(i32 %call1)
  %mul8 = mul nsw i32 3, %call7
  %add = add nsw i32 %call6, %mul8
  %add9 = add nsw i32 %add, 2
  %call10 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([28 x i8], [28 x i8]* @.str.2.66, i64 0, i64 0), i32 %call1, i32 %add9)
  %cmp11 = icmp sge i32 %argc, 3
  br i1 %cmp11, label %if.then12, label %if.end15

if.then12:                                        ; preds = %if.end5
  %arrayidx13 = getelementptr inbounds i8*, i8** %argv, i64 2
  %i1 = load i8*, i8** %arrayidx13, align 8
  %call14 = call i32 @atoi(i8* %i1) #11
  br label %if.end15

if.end15:                                         ; preds = %if.then12, %if.end5
  %x.0 = phi i32 [ %call14, %if.then12 ], [ 0, %if.end5 ]
  br label %while.cond

while.cond:                                       ; preds = %while.body, %if.end15
  %x.1 = phi i32 [ %x.0, %if.end15 ], [ %conv22, %while.body ]
  %call16 = call i32 @quantum_gcd(i32 %call1, i32 %x.1)
  %cmp17 = icmp sgt i32 %call16, 1
  br i1 %cmp17, label %lor.end, label %lor.rhs

lor.rhs:                                          ; preds = %while.cond
  %cmp18 = icmp slt i32 %x.1, 2
  br label %lor.end

lor.end:                                          ; preds = %lor.rhs, %while.cond
  %i2 = phi i1 [ true, %while.cond ], [ %cmp18, %lor.rhs ]
  br i1 %i2, label %while.body, label %while.end

while.body:                                       ; preds = %lor.end
  %call19 = call double @spec_rand()
  %mul20 = fmul double %call19, 0x41DFFFFFFFC00000
  %conv = fptosi double %mul20 to i64
  %conv21 = sext i32 %call1 to i64
  %rem = srem i64 %conv, %conv21
  %conv22 = trunc i64 %rem to i32
  br label %while.cond

while.end:                                        ; preds = %lor.end
  %call23 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.3.67, i64 0, i64 0), i32 %x.1)
  call void @quantum_new_qureg(%struct.quantum_reg_struct* sret(%struct.quantum_reg_struct) align 8 %tmp, i64 0, i32 %call6)
  %i3 = bitcast %struct.quantum_reg_struct* %qr to i8*
  %i4 = bitcast %struct.quantum_reg_struct* %tmp to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i3, i8* align 8 %i4, i64 32, i1 false)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %while.end
  %i.0 = phi i32 [ 0, %while.end ], [ %inc, %for.inc ]
  %cmp24 = icmp slt i32 %i.0, %call6
  br i1 %cmp24, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  call void @quantum_hadamard(i32 %i.0, %struct.quantum_reg_struct* %qr)
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %mul26 = mul nsw i32 3, %call7
  %add27 = add nsw i32 %mul26, 2
  call void @quantum_addscratch(i32 %add27, %struct.quantum_reg_struct* %qr)
  call void @quantum_exp_mod_n(i32 %call1, i32 %x.1, i32 %call6, i32 %call7, %struct.quantum_reg_struct* %qr)
  br label %for.cond28

for.cond28:                                       ; preds = %for.inc35, %for.end
  %i.1 = phi i32 [ 0, %for.end ], [ %inc36, %for.inc35 ]
  %mul29 = mul nsw i32 3, %call7
  %add30 = add nsw i32 %mul29, 2
  %cmp31 = icmp slt i32 %i.1, %add30
  br i1 %cmp31, label %for.body33, label %for.end37

for.body33:                                       ; preds = %for.cond28
  %call34 = call i32 @quantum_bmeasure(i32 0, %struct.quantum_reg_struct* %qr)
  br label %for.inc35

for.inc35:                                        ; preds = %for.body33
  %inc36 = add nsw i32 %i.1, 1
  br label %for.cond28

for.end37:                                        ; preds = %for.cond28
  call void @quantum_qft(i32 %call6, %struct.quantum_reg_struct* %qr)
  br label %for.cond38

for.cond38:                                       ; preds = %for.inc47, %for.end37
  %i.2 = phi i32 [ 0, %for.end37 ], [ %inc48, %for.inc47 ]
  %div = sdiv i32 %call6, 2
  %cmp39 = icmp slt i32 %i.2, %div
  br i1 %cmp39, label %for.body41, label %for.end49

for.body41:                                       ; preds = %for.cond38
  %sub = sub nsw i32 %call6, %i.2
  %sub42 = sub nsw i32 %sub, 1
  call void @quantum_cnot(i32 %i.2, i32 %sub42, %struct.quantum_reg_struct* %qr)
  %sub43 = sub nsw i32 %call6, %i.2
  %sub44 = sub nsw i32 %sub43, 1
  call void @quantum_cnot(i32 %sub44, i32 %i.2, %struct.quantum_reg_struct* %qr)
  %sub45 = sub nsw i32 %call6, %i.2
  %sub46 = sub nsw i32 %sub45, 1
  call void @quantum_cnot(i32 %i.2, i32 %sub46, %struct.quantum_reg_struct* %qr)
  br label %for.inc47

for.inc47:                                        ; preds = %for.body41
  %inc48 = add nsw i32 %i.2, 1
  br label %for.cond38

for.end49:                                        ; preds = %for.cond38
  %call50 = call i64 @quantum_measure(%struct.quantum_reg_struct* byval(%struct.quantum_reg_struct) align 8 %qr)
  %conv51 = trunc i64 %call50 to i32
  store i32 %conv51, i32* %c, align 4
  %i5 = load i32, i32* %c, align 4
  %cmp52 = icmp eq i32 %i5, -1
  br i1 %cmp52, label %if.then54, label %if.end56

if.then54:                                        ; preds = %for.end49
  %call55 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.4.68, i64 0, i64 0))
  call void @exit(i32 1) #10
  unreachable

if.end56:                                         ; preds = %for.end49
  %i6 = load i32, i32* %c, align 4
  %cmp57 = icmp eq i32 %i6, 0
  br i1 %cmp57, label %if.then59, label %if.end61

if.then59:                                        ; preds = %if.end56
  %call60 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.5.69, i64 0, i64 0))
  call void @exit(i32 2) #10
  unreachable

if.end61:                                         ; preds = %if.end56
  %shl = shl i32 1, %call6
  store i32 %shl, i32* %q, align 4
  %i7 = load i32, i32* %c, align 4
  %i8 = load i32, i32* %c, align 4
  %conv62 = sitofp i32 %i8 to float
  %i9 = load i32, i32* %q, align 4
  %conv63 = sitofp i32 %i9 to float
  %div64 = fdiv float %conv62, %conv63
  %conv65 = fpext float %div64 to double
  %call66 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.6.70, i64 0, i64 0), i32 %i7, double %conv65)
  call void @quantum_frac_approx(i32* %c, i32* %q, i32 %call6)
  %i10 = load i32, i32* %c, align 4
  %i11 = load i32, i32* %q, align 4
  %call67 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.7.71, i64 0, i64 0), i32 %i10, i32 %i11)
  %i12 = load i32, i32* %q, align 4
  %rem68 = srem i32 %i12, 2
  %cmp69 = icmp eq i32 %rem68, 1
  br i1 %cmp69, label %land.lhs.true, label %if.end78

land.lhs.true:                                    ; preds = %if.end61
  %i13 = load i32, i32* %q, align 4
  %mul71 = mul nsw i32 2, %i13
  %shl72 = shl i32 1, %call6
  %cmp73 = icmp slt i32 %mul71, %shl72
  br i1 %cmp73, label %if.then75, label %if.end78

if.then75:                                        ; preds = %land.lhs.true
  %call76 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @.str.8.72, i64 0, i64 0))
  %i14 = load i32, i32* %q, align 4
  %mul77 = mul nsw i32 %i14, 2
  store i32 %mul77, i32* %q, align 4
  br label %if.end78

if.end78:                                         ; preds = %if.then75, %land.lhs.true, %if.end61
  %i15 = load i32, i32* %q, align 4
  %rem79 = srem i32 %i15, 2
  %cmp80 = icmp eq i32 %rem79, 1
  br i1 %cmp80, label %if.then82, label %if.end84

if.then82:                                        ; preds = %if.end78
  %call83 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.9.73, i64 0, i64 0))
  call void @exit(i32 2) #10
  unreachable

if.end84:                                         ; preds = %if.end78
  %i16 = load i32, i32* %q, align 4
  %call85 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.10.74, i64 0, i64 0), i32 %i16)
  %i17 = load i32, i32* %q, align 4
  %div86 = sdiv i32 %i17, 2
  %call87 = call i32 @quantum_ipow(i32 %x.1, i32 %div86)
  %rem88 = srem i32 1, %call1
  %add89 = add nsw i32 %call87, %rem88
  %i18 = load i32, i32* %q, align 4
  %div90 = sdiv i32 %i18, 2
  %call91 = call i32 @quantum_ipow(i32 %x.1, i32 %div90)
  %rem92 = srem i32 1, %call1
  %sub93 = sub nsw i32 %call91, %rem92
  %call94 = call i32 @quantum_gcd(i32 %call1, i32 %add89)
  %call95 = call i32 @quantum_gcd(i32 %call1, i32 %sub93)
  %cmp96 = icmp sgt i32 %call94, %call95
  br i1 %cmp96, label %if.then98, label %if.else

if.then98:                                        ; preds = %if.end84
  br label %if.end99

if.else:                                          ; preds = %if.end84
  br label %if.end99

if.end99:                                         ; preds = %if.else, %if.then98
  %factor.0 = phi i32 [ %call94, %if.then98 ], [ %call95, %if.else ]
  %cmp100 = icmp slt i32 %factor.0, %call1
  br i1 %cmp100, label %land.lhs.true102, label %if.else108

land.lhs.true102:                                 ; preds = %if.end99
  %cmp103 = icmp sgt i32 %factor.0, 1
  br i1 %cmp103, label %if.then105, label %if.else108

if.then105:                                       ; preds = %land.lhs.true102
  %div106 = sdiv i32 %call1, %factor.0
  %call107 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.11.75, i64 0, i64 0), i32 %call1, i32 %factor.0, i32 %div106)
  br label %if.end110

if.else108:                                       ; preds = %land.lhs.true102, %if.end99
  %call109 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @.str.12, i64 0, i64 0))
  call void @exit(i32 0) #10
  unreachable

if.end110:                                        ; preds = %if.then105
  call void @quantum_delete_qureg(%struct.quantum_reg_struct* %qr)
  br label %return

return:                                           ; preds = %if.end110, %if.then3, %if.then
  %retval.0 = phi i32 [ 3, %if.then ], [ 3, %if.then3 ], [ 0, %if.end110 ]
  ret i32 %retval.0
}

; Function Attrs: nounwind readonly willreturn
declare dso_local i32 @atoi(i8*) #8

; Function Attrs: noinline nounwind uwtable
define dso_local i8* @quantum_get_version() #0 {
entry:
  ret i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.76, i64 0, i64 0)
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @spec_srand(i32 %seed) #0 {
entry:
  store i32 %seed, i32* @seedi, align 4
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local double @spec_rand() #0 {
entry:
  %i = load i32, i32* @seedi, align 4
  %conv = sext i32 %i to i64
  %div = sdiv i64 %conv, 127773
  %conv1 = trunc i64 %div to i32
  %i1 = load i32, i32* @seedi, align 4
  %conv2 = sext i32 %i1 to i64
  %rem = srem i64 %conv2, 127773
  %conv3 = trunc i64 %rem to i32
  %conv4 = sext i32 %conv3 to i64
  %mul = mul nsw i64 16807, %conv4
  %conv5 = sext i32 %conv1 to i64
  %mul6 = mul nsw i64 2836, %conv5
  %sub = sub nsw i64 %mul, %mul6
  %conv7 = trunc i64 %sub to i32
  %cmp = icmp sgt i32 %conv7, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  store i32 %conv7, i32* @seedi, align 4
  br label %if.end

if.else:                                          ; preds = %entry
  %conv9 = sext i32 %conv7 to i64
  %add = add nsw i64 %conv9, 2147483647
  %conv10 = trunc i64 %add to i32
  store i32 %conv10, i32* @seedi, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %i2 = load i32, i32* @seedi, align 4
  %conv11 = sitofp i32 %i2 to double
  %div12 = fdiv double %conv11, 0x41DFFFFFFFC00000
  ret double %div12
}

attributes #0 = { noinline nounwind uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nosync nounwind readnone speculatable willreturn }
attributes #2 = { noinline nounwind uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="64" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nofree nosync nounwind willreturn }
attributes #7 = { argmemonly nofree nosync nounwind willreturn }
attributes #8 = { nounwind readonly willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { nounwind }
attributes #10 = { noreturn nounwind }
attributes #11 = { nounwind readonly willreturn }

!llvm.ident = !{!0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0}
!llvm.module.flags = !{!1}

!0 = !{!"Ubuntu clang version 12.0.1-8build1"}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"branch_weights", i32 1, i32 1048575}
