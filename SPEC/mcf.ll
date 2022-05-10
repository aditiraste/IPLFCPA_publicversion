; ModuleID = 'mcf.ll'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.network = type { [200 x i8], [200 x i8], i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, double, i64, %struct.node*, %struct.node*, %struct.arc*, %struct.arc*, %struct.arc*, %struct.arc*, i64, i64, i64 }
%struct.node = type { i64, i32, %struct.node*, %struct.node*, %struct.node*, %struct.node*, %struct.arc*, %struct.arc*, %struct.arc*, %struct.arc*, i64, i64, i32, i32 }
%struct.arc = type { i64, %struct.node*, %struct.node*, i32, %struct.arc*, %struct.arc*, i64, i64 }
%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque
%struct.basket = type { %struct.arc*, i64, i64 }

@net = dso_local global %struct.network zeroinitializer, align 8
@.str = private unnamed_addr constant [34 x i8] c"active arcs                : %ld\0A\00", align 1
@.str.1 = private unnamed_addr constant [34 x i8] c"simplex iterations         : %ld\0A\00", align 1
@.str.2 = private unnamed_addr constant [36 x i8] c"objective value            : %0.0f\0A\00", align 1
@.str.3 = private unnamed_addr constant [34 x i8] c"erased arcs                : %ld\0A\00", align 1
@.str.4 = private unnamed_addr constant [34 x i8] c"new implicit arcs          : %ld\0A\00", align 1
@.str.5 = private unnamed_addr constant [29 x i8] c"not enough memory, exit(-1)\0A\00", align 1
@.str.6 = private unnamed_addr constant [34 x i8] c"checksum                   : %ld\0A\00", align 1
@.str.7 = private unnamed_addr constant [32 x i8] c"\0AMCF SPEC CPU2006 version 1.10\0A\00", align 1
@.str.8 = private unnamed_addr constant [52 x i8] c"Copyright (c) 1998-2000 Zuse Institut Berlin (ZIB)\0A\00", align 1
@.str.9 = private unnamed_addr constant [46 x i8] c"Copyright (c) 2000-2002 Andreas Loebel & ZIB\0A\00", align 1
@.str.10 = private unnamed_addr constant [40 x i8] c"Copyright (c) 2003-2005 Andreas Loebel\0A\00", align 1
@.str.11 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@.str.12 = private unnamed_addr constant [18 x i8] c"read error, exit\0A\00", align 1
@.str.13 = private unnamed_addr constant [34 x i8] c"nodes                      : %ld\0A\00", align 1
@.str.14 = private unnamed_addr constant [6 x i8] c"done\0A\00", align 1
@.str.15 = private unnamed_addr constant [8 x i8] c"mcf.out\00", align 1
@.str.16 = private unnamed_addr constant [25 x i8] c"PRIMAL NETWORK SIMPLEX: \00", align 1
@.str.1.17 = private unnamed_addr constant [49 x i8] c"artificial arc with nonzero flow, node %d (%ld)\0A\00", align 1
@.str.2.18 = private unnamed_addr constant [31 x i8] c"basis primal infeasible (%ld)\0A\00", align 1
@stderr = external dso_local global %struct._IO_FILE*, align 8
@.str.3.19 = private unnamed_addr constant [23 x i8] c"DUAL NETWORK SIMPLEX: \00", align 1
@.str.4.20 = private unnamed_addr constant [23 x i8] c"basis dual infeasible\0A\00", align 1
@.str.25 = private unnamed_addr constant [2 x i8] c"r\00", align 1
@.str.1.26 = private unnamed_addr constant [8 x i8] c"%ld %ld\00", align 1
@.str.2.27 = private unnamed_addr constant [31 x i8] c"read_min(): not enough memory\0A\00", align 1
@.str.3.28 = private unnamed_addr constant [12 x i8] c"%ld %ld %ld\00", align 1
@.str.29 = private unnamed_addr constant [31 x i8] c"network %s: not enough memory\0A\00", align 1
@stdout = external dso_local global %struct._IO_FILE*, align 8
@.str.38 = private unnamed_addr constant [2 x i8] c"w\00", align 1
@.str.1.39 = private unnamed_addr constant [4 x i8] c"()\0A\00", align 1
@.str.2.40 = private unnamed_addr constant [5 x i8] c"***\0A\00", align 1
@.str.3.41 = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
@perm = internal global [351 x %struct.basket*] zeroinitializer, align 16
@initialize = internal global i64 1, align 8
@basket = internal global [351 x %struct.basket] zeroinitializer, align 16
@nr_group = internal global i64 0, align 8
@group_pos = internal global i64 0, align 8
@basket_size = internal global i64 0, align 8

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @global_opt() #0 {
entry:
  %i = load i64, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 3), align 8
  %cmp = icmp sle i64 %i, 15000
  %i1 = zext i1 %cmp to i64
  %cond = select i1 %cmp, i32 5, i32 5
  %conv = sext i32 %cond to i64
  br label %while.cond

while.cond:                                       ; preds = %if.end23, %entry
  %residual_nb_it.0 = phi i64 [ %conv, %entry ], [ %dec, %if.end23 ]
  %new_arcs.0 = phi i64 [ -1, %entry ], [ %call14, %if.end23 ]
  %tobool = icmp ne i64 %new_arcs.0, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %i2 = load i64, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 5), align 8
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str, i64 0, i64 0), i64 %i2)
  %call1 = call i64 @primal_net_simplex(%struct.network* @net)
  %i3 = load i64, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 27), align 8
  %call2 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.1, i64 0, i64 0), i64 %i3)
  %call3 = call double @flow_cost(%struct.network* @net)
  %call4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.2, i64 0, i64 0), double %call3)
  %tobool5 = icmp ne i64 %residual_nb_it.0, 0
  br i1 %tobool5, label %if.end, label %if.then

if.then:                                          ; preds = %while.body
  br label %while.end

if.end:                                           ; preds = %while.body
  %i4 = load i64, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 7), align 8
  %tobool6 = icmp ne i64 %i4, 0
  br i1 %tobool6, label %if.then7, label %if.end13

if.then7:                                         ; preds = %if.end
  %call8 = call i64 @suspend_impl(%struct.network* @net, i64 -1, i64 0)
  %tobool9 = icmp ne i64 %call8, 0
  br i1 %tobool9, label %if.then10, label %if.end12

if.then10:                                        ; preds = %if.then7
  %call11 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.3, i64 0, i64 0), i64 %call8)
  br label %if.end12

if.end12:                                         ; preds = %if.then10, %if.then7
  br label %if.end13

if.end13:                                         ; preds = %if.end12, %if.end
  %call14 = call i64 @price_out_impl(%struct.network* @net)
  %tobool15 = icmp ne i64 %call14, 0
  br i1 %tobool15, label %if.then16, label %if.end18

if.then16:                                        ; preds = %if.end13
  %call17 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.4, i64 0, i64 0), i64 %call14)
  br label %if.end18

if.end18:                                         ; preds = %if.then16, %if.end13
  %cmp19 = icmp slt i64 %call14, 0
  br i1 %cmp19, label %if.then21, label %if.end23

if.then21:                                        ; preds = %if.end18
  %call22 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.5, i64 0, i64 0))
  call void @exit(i32 -1) #6
  unreachable

if.end23:                                         ; preds = %if.end18
  %dec = add nsw i64 %residual_nb_it.0, -1
  br label %while.cond

while.end:                                        ; preds = %if.then, %while.cond
  %i5 = load i64, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 29), align 8
  %call24 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.6, i64 0, i64 0), i64 %i5)
  ret i64 0
}

declare dso_local i32 @printf(i8*, ...) #1

; Function Attrs: noreturn nounwind
declare dso_local void @exit(i32) #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main(i32 %argc, i8** %argv) #0 {
entry:
  %cmp = icmp slt i32 %argc, 2
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([32 x i8], [32 x i8]* @.str.7, i64 0, i64 0))
  %call1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.8, i64 0, i64 0))
  %call2 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.9, i64 0, i64 0))
  %call3 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.10, i64 0, i64 0))
  %call4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0))
  call void @llvm.memset.p0i8.i64(i8* align 8 getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 0, i32 0), i8 0, i64 624, i1 false)
  store i64 10000000, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 18), align 8
  %arrayidx = getelementptr inbounds i8*, i8** %argv, i64 1
  %i = load i8*, i8** %arrayidx, align 8
  %call5 = call i8* @strcpy(i8* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 0, i64 0), i8* %i) #7
  %call6 = call i64 @read_min(%struct.network* @net)
  %tobool = icmp ne i64 %call6, 0
  br i1 %tobool, label %if.then7, label %if.end10

if.then7:                                         ; preds = %if.end
  %call8 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.12, i64 0, i64 0))
  %call9 = call i64 @getfree(%struct.network* @net)
  br label %return

if.end10:                                         ; preds = %if.end
  %i1 = load i64, i64* getelementptr inbounds (%struct.network, %struct.network* @net, i32 0, i32 3), align 8
  %call11 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.13, i64 0, i64 0), i64 %i1)
  %call12 = call i64 @primal_start_artificial(%struct.network* @net)
  %call13 = call i64 @global_opt()
  %call14 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.14, i64 0, i64 0))
  %call15 = call i64 @write_circulations(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.15, i64 0, i64 0), %struct.network* @net)
  %tobool16 = icmp ne i64 %call15, 0
  br i1 %tobool16, label %if.then17, label %if.end19

if.then17:                                        ; preds = %if.end10
  %call18 = call i64 @getfree(%struct.network* @net)
  br label %return

if.end19:                                         ; preds = %if.end10
  %call20 = call i64 @getfree(%struct.network* @net)
  br label %return

return:                                           ; preds = %if.end19, %if.then17, %if.then7, %if.then
  %retval.0 = phi i32 [ -1, %if.then ], [ -1, %if.then7 ], [ -1, %if.then17 ], [ 0, %if.end19 ]
  ret i32 %retval.0
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #3

; Function Attrs: nounwind
declare dso_local i8* @strcpy(i8*, i8*) #4

; Function Attrs: noinline nounwind uwtable
define dso_local void @refresh_neighbour_lists(%struct.network* %net) #0 {
entry:
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i = load %struct.node*, %struct.node** %nodes, align 8
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  %i1 = load %struct.node*, %struct.node** %stop_nodes, align 8
  %i2 = bitcast %struct.node* %i1 to i8*
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %node.0 = phi %struct.node* [ %i, %entry ], [ %incdec.ptr, %for.inc ]
  %i3 = bitcast i8* %i2 to %struct.node*
  %cmp = icmp ult %struct.node* %node.0, %i3
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %firstin = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 8
  store %struct.arc* null, %struct.arc** %firstin, align 8
  %firstout = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 7
  store %struct.arc* null, %struct.arc** %firstout, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %incdec.ptr = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i4 = load %struct.arc*, %struct.arc** %arcs, align 8
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i5 = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %i6 = bitcast %struct.arc* %i5 to i8*
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc10, %for.end
  %arc.0 = phi %struct.arc* [ %i4, %for.end ], [ %incdec.ptr11, %for.inc10 ]
  %i7 = bitcast i8* %i6 to %struct.arc*
  %cmp2 = icmp ult %struct.arc* %arc.0, %i7
  br i1 %cmp2, label %for.body3, label %for.end12

for.body3:                                        ; preds = %for.cond1
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i8 = load %struct.node*, %struct.node** %tail, align 8
  %firstout4 = getelementptr inbounds %struct.node, %struct.node* %i8, i32 0, i32 7
  %i9 = load %struct.arc*, %struct.arc** %firstout4, align 8
  %nextout = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 4
  store %struct.arc* %i9, %struct.arc** %nextout, align 8
  %tail5 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i10 = load %struct.node*, %struct.node** %tail5, align 8
  %firstout6 = getelementptr inbounds %struct.node, %struct.node* %i10, i32 0, i32 7
  store %struct.arc* %arc.0, %struct.arc** %firstout6, align 8
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i11 = load %struct.node*, %struct.node** %head, align 8
  %firstin7 = getelementptr inbounds %struct.node, %struct.node* %i11, i32 0, i32 8
  %i12 = load %struct.arc*, %struct.arc** %firstin7, align 8
  %nextin = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 5
  store %struct.arc* %i12, %struct.arc** %nextin, align 8
  %head8 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i13 = load %struct.node*, %struct.node** %head8, align 8
  %firstin9 = getelementptr inbounds %struct.node, %struct.node* %i13, i32 0, i32 8
  store %struct.arc* %arc.0, %struct.arc** %firstin9, align 8
  br label %for.inc10

for.inc10:                                        ; preds = %for.body3
  %incdec.ptr11 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  br label %for.cond1

for.end12:                                        ; preds = %for.cond1
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @refresh_potential(%struct.network* %net) #0 {
entry:
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i = load %struct.node*, %struct.node** %nodes, align 8
  %potential = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 0
  store i64 -100000000, i64* %potential, align 8
  %child = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 2
  %i1 = load %struct.node*, %struct.node** %child, align 8
  br label %while.cond

while.cond:                                       ; preds = %while.end21, %entry
  %tmp.0 = phi %struct.node* [ %i1, %entry ], [ %tmp.3, %while.end21 ]
  %node.0 = phi %struct.node* [ %i1, %entry ], [ %node.3, %while.end21 ]
  %checksum.0 = phi i64 [ 0, %entry ], [ %checksum.1, %while.end21 ]
  %cmp = icmp ne %struct.node* %node.0, %i
  br i1 %cmp, label %while.body, label %while.end22

while.body:                                       ; preds = %while.cond
  br label %while.cond1

while.cond1:                                      ; preds = %if.end, %while.body
  %tmp.1 = phi %struct.node* [ %tmp.0, %while.body ], [ %node.1, %if.end ]
  %node.1 = phi %struct.node* [ %node.0, %while.body ], [ %i11, %if.end ]
  %checksum.1 = phi i64 [ %checksum.0, %while.body ], [ %checksum.2, %if.end ]
  %tobool = icmp ne %struct.node* %node.1, null
  br i1 %tobool, label %while.body2, label %while.end

while.body2:                                      ; preds = %while.cond1
  %orientation = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 1
  %i2 = load i32, i32* %orientation, align 8
  %cmp3 = icmp eq i32 %i2, 1
  br i1 %cmp3, label %if.then, label %if.else

if.then:                                          ; preds = %while.body2
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 6
  %i3 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %i3, i32 0, i32 0
  %i4 = load i64, i64* %cost, align 8
  %pred = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 3
  %i5 = load %struct.node*, %struct.node** %pred, align 8
  %potential4 = getelementptr inbounds %struct.node, %struct.node* %i5, i32 0, i32 0
  %i6 = load i64, i64* %potential4, align 8
  %add = add nsw i64 %i4, %i6
  %potential5 = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 0
  store i64 %add, i64* %potential5, align 8
  br label %if.end

if.else:                                          ; preds = %while.body2
  %pred6 = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 3
  %i7 = load %struct.node*, %struct.node** %pred6, align 8
  %potential7 = getelementptr inbounds %struct.node, %struct.node* %i7, i32 0, i32 0
  %i8 = load i64, i64* %potential7, align 8
  %basic_arc8 = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 6
  %i9 = load %struct.arc*, %struct.arc** %basic_arc8, align 8
  %cost9 = getelementptr inbounds %struct.arc, %struct.arc* %i9, i32 0, i32 0
  %i10 = load i64, i64* %cost9, align 8
  %sub = sub nsw i64 %i8, %i10
  %potential10 = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 0
  store i64 %sub, i64* %potential10, align 8
  %inc = add nsw i64 %checksum.1, 1
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %checksum.2 = phi i64 [ %checksum.1, %if.then ], [ %inc, %if.else ]
  %child11 = getelementptr inbounds %struct.node, %struct.node* %node.1, i32 0, i32 2
  %i11 = load %struct.node*, %struct.node** %child11, align 8
  br label %while.cond1

while.end:                                        ; preds = %while.cond1
  br label %while.cond12

while.cond12:                                     ; preds = %if.end20, %while.end
  %tmp.2 = phi %struct.node* [ %tmp.1, %while.end ], [ %i13, %if.end20 ]
  %node.2 = phi %struct.node* [ %tmp.1, %while.end ], [ %i14, %if.end20 ]
  %pred13 = getelementptr inbounds %struct.node, %struct.node* %node.2, i32 0, i32 3
  %i12 = load %struct.node*, %struct.node** %pred13, align 8
  %tobool14 = icmp ne %struct.node* %i12, null
  br i1 %tobool14, label %while.body15, label %while.end21

while.body15:                                     ; preds = %while.cond12
  %sibling = getelementptr inbounds %struct.node, %struct.node* %node.2, i32 0, i32 4
  %i13 = load %struct.node*, %struct.node** %sibling, align 8
  %tobool16 = icmp ne %struct.node* %i13, null
  br i1 %tobool16, label %if.then17, label %if.else18

if.then17:                                        ; preds = %while.body15
  br label %while.end21

if.else18:                                        ; preds = %while.body15
  %pred19 = getelementptr inbounds %struct.node, %struct.node* %node.2, i32 0, i32 3
  %i14 = load %struct.node*, %struct.node** %pred19, align 8
  br label %if.end20

if.end20:                                         ; preds = %if.else18
  br label %while.cond12

while.end21:                                      ; preds = %if.then17, %while.cond12
  %tmp.3 = phi %struct.node* [ %i13, %if.then17 ], [ %tmp.2, %while.cond12 ]
  %node.3 = phi %struct.node* [ %i13, %if.then17 ], [ %node.2, %while.cond12 ]
  br label %while.cond

while.end22:                                      ; preds = %while.cond
  ret i64 %checksum.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local double @flow_cost(%struct.network* %net) #0 {
entry:
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %i1 = bitcast %struct.arc* %i to i8*
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i2 = load %struct.arc*, %struct.arc** %arcs, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %arc.0 = phi %struct.arc* [ %i2, %entry ], [ %incdec.ptr, %for.inc ]
  %i3 = bitcast i8* %i1 to %struct.arc*
  %cmp = icmp ne %struct.arc* %arc.0, %i3
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i4 = load i32, i32* %ident, align 8
  %cmp1 = icmp eq i32 %i4, 2
  br i1 %cmp1, label %if.then, label %if.else

if.then:                                          ; preds = %for.body
  %flow = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 6
  store i64 1, i64* %flow, align 8
  br label %if.end

if.else:                                          ; preds = %for.body
  %flow2 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 6
  store i64 0, i64* %flow2, align 8
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %incdec.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  %i5 = load %struct.node*, %struct.node** %stop_nodes, align 8
  %i6 = bitcast %struct.node* %i5 to i8*
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i7 = load %struct.node*, %struct.node** %nodes, align 8
  %incdec.ptr3 = getelementptr inbounds %struct.node, %struct.node* %i7, i32 1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc9, %for.end
  %node.0 = phi %struct.node* [ %incdec.ptr3, %for.end ], [ %incdec.ptr10, %for.inc9 ]
  %i8 = bitcast i8* %i6 to %struct.node*
  %cmp5 = icmp ne %struct.node* %node.0, %i8
  br i1 %cmp5, label %for.body6, label %for.end11

for.body6:                                        ; preds = %for.cond4
  %flow7 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 10
  %i9 = load i64, i64* %flow7, align 8
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 6
  %i10 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %flow8 = getelementptr inbounds %struct.arc, %struct.arc* %i10, i32 0, i32 6
  store i64 %i9, i64* %flow8, align 8
  br label %for.inc9

for.inc9:                                         ; preds = %for.body6
  %incdec.ptr10 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 1
  br label %for.cond4

for.end11:                                        ; preds = %for.cond4
  %stop_arcs12 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i11 = load %struct.arc*, %struct.arc** %stop_arcs12, align 8
  %i12 = bitcast %struct.arc* %i11 to i8*
  %arcs13 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i13 = load %struct.arc*, %struct.arc** %arcs13, align 8
  br label %for.cond14

for.cond14:                                       ; preds = %for.inc33, %for.end11
  %fleet.0 = phi i64 [ 0, %for.end11 ], [ %fleet.3, %for.inc33 ]
  %arc.1 = phi %struct.arc* [ %i13, %for.end11 ], [ %incdec.ptr34, %for.inc33 ]
  %operational_cost.0 = phi i64 [ 0, %for.end11 ], [ %operational_cost.3, %for.inc33 ]
  %i14 = bitcast i8* %i12 to %struct.arc*
  %cmp15 = icmp ne %struct.arc* %arc.1, %i14
  br i1 %cmp15, label %for.body16, label %for.end35

for.body16:                                       ; preds = %for.cond14
  %flow17 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 6
  %i15 = load i64, i64* %flow17, align 8
  %tobool = icmp ne i64 %i15, 0
  br i1 %tobool, label %if.then18, label %if.end32

if.then18:                                        ; preds = %for.body16
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  %i16 = load %struct.node*, %struct.node** %tail, align 8
  %number = getelementptr inbounds %struct.node, %struct.node* %i16, i32 0, i32 12
  %i17 = load i32, i32* %number, align 8
  %cmp19 = icmp slt i32 %i17, 0
  br i1 %cmp19, label %land.lhs.true, label %if.then22

land.lhs.true:                                    ; preds = %if.then18
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 2
  %i18 = load %struct.node*, %struct.node** %head, align 8
  %number20 = getelementptr inbounds %struct.node, %struct.node* %i18, i32 0, i32 12
  %i19 = load i32, i32* %number20, align 8
  %cmp21 = icmp sgt i32 %i19, 0
  br i1 %cmp21, label %if.end31, label %if.then22

if.then22:                                        ; preds = %land.lhs.true, %if.then18
  %tail23 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  %i20 = load %struct.node*, %struct.node** %tail23, align 8
  %number24 = getelementptr inbounds %struct.node, %struct.node* %i20, i32 0, i32 12
  %i21 = load i32, i32* %number24, align 8
  %tobool25 = icmp ne i32 %i21, 0
  br i1 %tobool25, label %if.else27, label %if.then26

if.then26:                                        ; preds = %if.then22
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 0
  %i22 = load i64, i64* %cost, align 8
  %bigM = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i23 = load i64, i64* %bigM, align 8
  %sub = sub nsw i64 %i22, %i23
  %add = add nsw i64 %operational_cost.0, %sub
  %inc = add nsw i64 %fleet.0, 1
  br label %if.end30

if.else27:                                        ; preds = %if.then22
  %cost28 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 0
  %i24 = load i64, i64* %cost28, align 8
  %add29 = add nsw i64 %operational_cost.0, %i24
  br label %if.end30

if.end30:                                         ; preds = %if.else27, %if.then26
  %fleet.1 = phi i64 [ %fleet.0, %if.else27 ], [ %inc, %if.then26 ]
  %operational_cost.1 = phi i64 [ %add29, %if.else27 ], [ %add, %if.then26 ]
  br label %if.end31

if.end31:                                         ; preds = %if.end30, %land.lhs.true
  %fleet.2 = phi i64 [ %fleet.0, %land.lhs.true ], [ %fleet.1, %if.end30 ]
  %operational_cost.2 = phi i64 [ %operational_cost.0, %land.lhs.true ], [ %operational_cost.1, %if.end30 ]
  br label %if.end32

if.end32:                                         ; preds = %if.end31, %for.body16
  %fleet.3 = phi i64 [ %fleet.2, %if.end31 ], [ %fleet.0, %for.body16 ]
  %operational_cost.3 = phi i64 [ %operational_cost.2, %if.end31 ], [ %operational_cost.0, %for.body16 ]
  br label %for.inc33

for.inc33:                                        ; preds = %if.end32
  %incdec.ptr34 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 1
  br label %for.cond14

for.end35:                                        ; preds = %for.cond14
  %conv = sitofp i64 %fleet.0 to double
  %bigM36 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i25 = load i64, i64* %bigM36, align 8
  %conv37 = sitofp i64 %i25 to double
  %mul = fmul double %conv, %conv37
  %conv38 = sitofp i64 %operational_cost.0 to double
  %add39 = fadd double %mul, %conv38
  ret double %add39
}

; Function Attrs: noinline nounwind uwtable
define dso_local double @flow_org_cost(%struct.network* %net) #0 {
entry:
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %i1 = bitcast %struct.arc* %i to i8*
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i2 = load %struct.arc*, %struct.arc** %arcs, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %arc.0 = phi %struct.arc* [ %i2, %entry ], [ %incdec.ptr, %for.inc ]
  %i3 = bitcast i8* %i1 to %struct.arc*
  %cmp = icmp ne %struct.arc* %arc.0, %i3
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i4 = load i32, i32* %ident, align 8
  %cmp1 = icmp eq i32 %i4, 2
  br i1 %cmp1, label %if.then, label %if.else

if.then:                                          ; preds = %for.body
  %flow = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 6
  store i64 1, i64* %flow, align 8
  br label %if.end

if.else:                                          ; preds = %for.body
  %flow2 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 6
  store i64 0, i64* %flow2, align 8
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %incdec.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  %i5 = load %struct.node*, %struct.node** %stop_nodes, align 8
  %i6 = bitcast %struct.node* %i5 to i8*
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i7 = load %struct.node*, %struct.node** %nodes, align 8
  %incdec.ptr3 = getelementptr inbounds %struct.node, %struct.node* %i7, i32 1
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc9, %for.end
  %node.0 = phi %struct.node* [ %incdec.ptr3, %for.end ], [ %incdec.ptr10, %for.inc9 ]
  %i8 = bitcast i8* %i6 to %struct.node*
  %cmp5 = icmp ne %struct.node* %node.0, %i8
  br i1 %cmp5, label %for.body6, label %for.end11

for.body6:                                        ; preds = %for.cond4
  %flow7 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 10
  %i9 = load i64, i64* %flow7, align 8
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 6
  %i10 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %flow8 = getelementptr inbounds %struct.arc, %struct.arc* %i10, i32 0, i32 6
  store i64 %i9, i64* %flow8, align 8
  br label %for.inc9

for.inc9:                                         ; preds = %for.body6
  %incdec.ptr10 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 1
  br label %for.cond4

for.end11:                                        ; preds = %for.cond4
  %stop_arcs12 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i11 = load %struct.arc*, %struct.arc** %stop_arcs12, align 8
  %i12 = bitcast %struct.arc* %i11 to i8*
  %arcs13 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i13 = load %struct.arc*, %struct.arc** %arcs13, align 8
  br label %for.cond14

for.cond14:                                       ; preds = %for.inc33, %for.end11
  %fleet.0 = phi i64 [ 0, %for.end11 ], [ %fleet.3, %for.inc33 ]
  %arc.1 = phi %struct.arc* [ %i13, %for.end11 ], [ %incdec.ptr34, %for.inc33 ]
  %operational_cost.0 = phi i64 [ 0, %for.end11 ], [ %operational_cost.3, %for.inc33 ]
  %i14 = bitcast i8* %i12 to %struct.arc*
  %cmp15 = icmp ne %struct.arc* %arc.1, %i14
  br i1 %cmp15, label %for.body16, label %for.end35

for.body16:                                       ; preds = %for.cond14
  %flow17 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 6
  %i15 = load i64, i64* %flow17, align 8
  %tobool = icmp ne i64 %i15, 0
  br i1 %tobool, label %if.then18, label %if.end32

if.then18:                                        ; preds = %for.body16
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  %i16 = load %struct.node*, %struct.node** %tail, align 8
  %number = getelementptr inbounds %struct.node, %struct.node* %i16, i32 0, i32 12
  %i17 = load i32, i32* %number, align 8
  %cmp19 = icmp slt i32 %i17, 0
  br i1 %cmp19, label %land.lhs.true, label %if.then22

land.lhs.true:                                    ; preds = %if.then18
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 2
  %i18 = load %struct.node*, %struct.node** %head, align 8
  %number20 = getelementptr inbounds %struct.node, %struct.node* %i18, i32 0, i32 12
  %i19 = load i32, i32* %number20, align 8
  %cmp21 = icmp sgt i32 %i19, 0
  br i1 %cmp21, label %if.end31, label %if.then22

if.then22:                                        ; preds = %land.lhs.true, %if.then18
  %tail23 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  %i20 = load %struct.node*, %struct.node** %tail23, align 8
  %number24 = getelementptr inbounds %struct.node, %struct.node* %i20, i32 0, i32 12
  %i21 = load i32, i32* %number24, align 8
  %tobool25 = icmp ne i32 %i21, 0
  br i1 %tobool25, label %if.else27, label %if.then26

if.then26:                                        ; preds = %if.then22
  %org_cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 7
  %i22 = load i64, i64* %org_cost, align 8
  %bigM = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i23 = load i64, i64* %bigM, align 8
  %sub = sub nsw i64 %i22, %i23
  %add = add nsw i64 %operational_cost.0, %sub
  %inc = add nsw i64 %fleet.0, 1
  br label %if.end30

if.else27:                                        ; preds = %if.then22
  %org_cost28 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 7
  %i24 = load i64, i64* %org_cost28, align 8
  %add29 = add nsw i64 %operational_cost.0, %i24
  br label %if.end30

if.end30:                                         ; preds = %if.else27, %if.then26
  %fleet.1 = phi i64 [ %fleet.0, %if.else27 ], [ %inc, %if.then26 ]
  %operational_cost.1 = phi i64 [ %add29, %if.else27 ], [ %add, %if.then26 ]
  br label %if.end31

if.end31:                                         ; preds = %if.end30, %land.lhs.true
  %fleet.2 = phi i64 [ %fleet.0, %land.lhs.true ], [ %fleet.1, %if.end30 ]
  %operational_cost.2 = phi i64 [ %operational_cost.0, %land.lhs.true ], [ %operational_cost.1, %if.end30 ]
  br label %if.end32

if.end32:                                         ; preds = %if.end31, %for.body16
  %fleet.3 = phi i64 [ %fleet.2, %if.end31 ], [ %fleet.0, %for.body16 ]
  %operational_cost.3 = phi i64 [ %operational_cost.2, %if.end31 ], [ %operational_cost.0, %for.body16 ]
  br label %for.inc33

for.inc33:                                        ; preds = %if.end32
  %incdec.ptr34 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 1
  br label %for.cond14

for.end35:                                        ; preds = %for.cond14
  %conv = sitofp i64 %fleet.0 to double
  %bigM36 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i25 = load i64, i64* %bigM36, align 8
  %conv37 = sitofp i64 %i25 to double
  %mul = fmul double %conv, %conv37
  %conv38 = sitofp i64 %operational_cost.0 to double
  %add39 = fadd double %mul, %conv38
  ret double %add39
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @primal_feasible(%struct.network* %net) #0 {
entry:
  %dummy_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  %i = load %struct.arc*, %struct.arc** %dummy_arcs, align 8
  %stop_dummy1 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 26
  %i1 = load %struct.arc*, %struct.arc** %stop_dummy1, align 8
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i2 = load %struct.node*, %struct.node** %nodes, align 8
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  %i3 = load %struct.node*, %struct.node** %stop_nodes, align 8
  %i4 = bitcast %struct.node* %i3 to i8*
  %incdec.ptr = getelementptr inbounds %struct.node, %struct.node* %i2, i32 1
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %node.0 = phi %struct.node* [ %incdec.ptr, %entry ], [ %incdec.ptr20, %for.inc ]
  %i5 = bitcast i8* %i4 to %struct.node*
  %cmp = icmp ult %struct.node* %node.0, %i5
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 6
  %i6 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %flow2 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 10
  %i7 = load i64, i64* %flow2, align 8
  %cmp3 = icmp uge %struct.arc* %i6, %i
  br i1 %cmp3, label %land.lhs.true, label %if.else

land.lhs.true:                                    ; preds = %for.body
  %cmp4 = icmp ult %struct.arc* %i6, %i1
  br i1 %cmp4, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true
  %cmp5 = icmp sge i64 %i7, 0
  br i1 %cmp5, label %cond.true, label %cond.false

cond.true:                                        ; preds = %if.then
  br label %cond.end

cond.false:                                       ; preds = %if.then
  %sub = sub nsw i64 0, %i7
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i64 [ %i7, %cond.true ], [ %sub, %cond.false ]
  %feas_tol = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 16
  %i8 = load i64, i64* %feas_tol, align 8
  %cmp6 = icmp sgt i64 %cond, %i8
  br i1 %cmp6, label %if.then7, label %if.end

if.then7:                                         ; preds = %cond.end
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.16, i64 0, i64 0))
  %number = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 12
  %i9 = load i32, i32* %number, align 8
  %call8 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.1.17, i64 0, i64 0), i32 %i9, i64 %i7)
  br label %if.end

if.end:                                           ; preds = %if.then7, %cond.end
  br label %if.end19

if.else:                                          ; preds = %land.lhs.true, %for.body
  %feas_tol9 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 16
  %i10 = load i64, i64* %feas_tol9, align 8
  %sub10 = sub nsw i64 0, %i10
  %cmp11 = icmp slt i64 %i7, %sub10
  br i1 %cmp11, label %if.then15, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %if.else
  %sub12 = sub nsw i64 %i7, 1
  %feas_tol13 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 16
  %i11 = load i64, i64* %feas_tol13, align 8
  %cmp14 = icmp sgt i64 %sub12, %i11
  br i1 %cmp14, label %if.then15, label %if.end18

if.then15:                                        ; preds = %lor.lhs.false, %if.else
  %call16 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.16, i64 0, i64 0))
  %call17 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.2.18, i64 0, i64 0), i64 %i7)
  %feasible = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 13
  store i64 0, i64* %feasible, align 8
  br label %return

if.end18:                                         ; preds = %lor.lhs.false
  br label %if.end19

if.end19:                                         ; preds = %if.end18, %if.end
  br label %for.inc

for.inc:                                          ; preds = %if.end19
  %incdec.ptr20 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %feasible21 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 13
  store i64 1, i64* %feasible21, align 8
  br label %return

return:                                           ; preds = %for.end, %if.then15
  %retval.0 = phi i64 [ 1, %if.then15 ], [ 0, %for.end ]
  ret i64 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @dual_feasible(%struct.network* %net) #0 {
entry:
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i1 = load %struct.arc*, %struct.arc** %arcs, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %arc.0 = phi %struct.arc* [ %i1, %entry ], [ %incdec.ptr, %for.inc ]
  %cmp = icmp ult %struct.arc* %arc.0, %i
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 0
  %i2 = load i64, i64* %cost, align 8
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i3 = load %struct.node*, %struct.node** %tail, align 8
  %potential = getelementptr inbounds %struct.node, %struct.node* %i3, i32 0, i32 0
  %i4 = load i64, i64* %potential, align 8
  %sub = sub nsw i64 %i2, %i4
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i5 = load %struct.node*, %struct.node** %head, align 8
  %potential1 = getelementptr inbounds %struct.node, %struct.node* %i5, i32 0, i32 0
  %i6 = load i64, i64* %potential1, align 8
  %add = add nsw i64 %sub, %i6
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i7 = load i32, i32* %ident, align 8
  switch i32 %i7, label %sw.default [
    i32 0, label %sw.bb
    i32 1, label %sw.bb
    i32 2, label %sw.bb4
    i32 -1, label %sw.bb9
  ]

sw.bb:                                            ; preds = %for.body, %for.body
  %feas_tol = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 16
  %i8 = load i64, i64* %feas_tol, align 8
  %sub2 = sub nsw i64 0, %i8
  %cmp3 = icmp slt i64 %add, %sub2
  br i1 %cmp3, label %if.then, label %if.end

if.then:                                          ; preds = %sw.bb
  br label %DUAL_INFEAS

if.end:                                           ; preds = %sw.bb
  br label %sw.epilog

sw.bb4:                                           ; preds = %for.body
  %feas_tol5 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 16
  %i9 = load i64, i64* %feas_tol5, align 8
  %cmp6 = icmp sgt i64 %add, %i9
  br i1 %cmp6, label %if.then7, label %if.end8

if.then7:                                         ; preds = %sw.bb4
  br label %DUAL_INFEAS

if.end8:                                          ; preds = %sw.bb4
  br label %sw.epilog

sw.bb9:                                           ; preds = %for.body
  br label %sw.default

sw.default:                                       ; preds = %sw.bb9, %for.body
  br label %sw.epilog

sw.epilog:                                        ; preds = %sw.default, %if.end8, %if.end
  br label %for.inc

for.inc:                                          ; preds = %sw.epilog
  %incdec.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %return

DUAL_INFEAS:                                      ; preds = %if.then7, %if.then
  %i10 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %call = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %i10, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.3.19, i64 0, i64 0))
  %i11 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %call10 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %i11, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.4.20, i64 0, i64 0))
  br label %return

return:                                           ; preds = %DUAL_INFEAS, %for.end
  %retval.0 = phi i64 [ 1, %DUAL_INFEAS ], [ 0, %for.end ]
  ret i64 %retval.0
}

declare dso_local i32 @fprintf(%struct._IO_FILE*, i8*, ...) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @getfree(%struct.network* %net) #0 {
entry:
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i = load %struct.node*, %struct.node** %nodes, align 8
  %tobool = icmp ne %struct.node* %i, null
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %nodes1 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i1 = load %struct.node*, %struct.node** %nodes1, align 8
  %i2 = bitcast %struct.node* %i1 to i8*
  call void @free(i8* %i2) #7
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i3 = load %struct.arc*, %struct.arc** %arcs, align 8
  %tobool2 = icmp ne %struct.arc* %i3, null
  br i1 %tobool2, label %if.then3, label %if.end5

if.then3:                                         ; preds = %if.end
  %arcs4 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i4 = load %struct.arc*, %struct.arc** %arcs4, align 8
  %i5 = bitcast %struct.arc* %i4 to i8*
  call void @free(i8* %i5) #7
  br label %if.end5

if.end5:                                          ; preds = %if.then3, %if.end
  %dummy_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  %i6 = load %struct.arc*, %struct.arc** %dummy_arcs, align 8
  %tobool6 = icmp ne %struct.arc* %i6, null
  br i1 %tobool6, label %if.then7, label %if.end9

if.then7:                                         ; preds = %if.end5
  %dummy_arcs8 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  %i7 = load %struct.arc*, %struct.arc** %dummy_arcs8, align 8
  %i8 = bitcast %struct.arc* %i7 to i8*
  call void @free(i8* %i8) #7
  br label %if.end9

if.end9:                                          ; preds = %if.then7, %if.end5
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  store %struct.node* null, %struct.node** %stop_nodes, align 8
  %nodes10 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  store %struct.node* null, %struct.node** %nodes10, align 8
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  store %struct.arc* null, %struct.arc** %stop_arcs, align 8
  %arcs11 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  store %struct.arc* null, %struct.arc** %arcs11, align 8
  %stop_dummy = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 26
  store %struct.arc* null, %struct.arc** %stop_dummy, align 8
  %dummy_arcs12 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  store %struct.arc* null, %struct.arc** %dummy_arcs12, align 8
  ret i64 0
}

; Function Attrs: nounwind
declare dso_local void @free(i8*) #4

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @read_min(%struct.network* %net) #0 {
entry:
  %instring = alloca [201 x i8], align 16
  %t = alloca i64, align 8
  %h = alloca i64, align 8
  %c = alloca i64, align 8
  %inputfile = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 0
  %arraydecay = getelementptr inbounds [200 x i8], [200 x i8]* %inputfile, i64 0, i64 0
  %call = call noalias %struct._IO_FILE* @fopen(i8* %arraydecay, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.25, i64 0, i64 0))
  %cmp = icmp eq %struct._IO_FILE* %call, null
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %arraydecay1 = getelementptr inbounds [201 x i8], [201 x i8]* %instring, i64 0, i64 0
  %call2 = call i8* @fgets(i8* %arraydecay1, i32 200, %struct._IO_FILE* %call)
  %arraydecay3 = getelementptr inbounds [201 x i8], [201 x i8]* %instring, i64 0, i64 0
  %call4 = call i32 (i8*, i8*, ...) @__isoc99_sscanf(i8* %arraydecay3, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.1.26, i64 0, i64 0), i64* %t, i64* %h) #7
  %cmp5 = icmp ne i32 %call4, 2
  br i1 %cmp5, label %if.then6, label %if.end7

if.then6:                                         ; preds = %if.end
  br label %return

if.end7:                                          ; preds = %if.end
  %i = load i64, i64* %t, align 8
  %n_trips = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  store i64 %i, i64* %n_trips, align 8
  %i1 = load i64, i64* %h, align 8
  %m_org = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 6
  store i64 %i1, i64* %m_org, align 8
  %i2 = load i64, i64* %t, align 8
  %i3 = load i64, i64* %t, align 8
  %add = add nsw i64 %i2, %i3
  %add8 = add nsw i64 %add, 1
  %n = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  store i64 %add8, i64* %n, align 8
  %i4 = load i64, i64* %t, align 8
  %i5 = load i64, i64* %t, align 8
  %add9 = add nsw i64 %i4, %i5
  %i6 = load i64, i64* %t, align 8
  %add10 = add nsw i64 %add9, %i6
  %i7 = load i64, i64* %h, align 8
  %add11 = add nsw i64 %add10, %i7
  %m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  store i64 %add11, i64* %m, align 8
  %n_trips12 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i8 = load i64, i64* %n_trips12, align 8
  %cmp13 = icmp sle i64 %i8, 15000
  br i1 %cmp13, label %if.then14, label %if.else

if.then14:                                        ; preds = %if.end7
  %m15 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i9 = load i64, i64* %m15, align 8
  %max_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  store i64 %i9, i64* %max_m, align 8
  %max_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 9
  store i64 3000000, i64* %max_new_m, align 8
  br label %if.end18

if.else:                                          ; preds = %if.end7
  %max_m16 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  store i64 27328512, i64* %max_m16, align 8
  %max_new_m17 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 9
  store i64 28900000, i64* %max_new_m17, align 8
  br label %if.end18

if.end18:                                         ; preds = %if.else, %if.then14
  %max_m19 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  %i10 = load i64, i64* %max_m19, align 8
  %m20 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i11 = load i64, i64* %m20, align 8
  %sub = sub nsw i64 %i10, %i11
  %max_residual_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  store i64 %sub, i64* %max_residual_new_m, align 8
  %n21 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i12 = load i64, i64* %n21, align 8
  %add22 = add nsw i64 %i12, 1
  %call23 = call noalias i8* @calloc(i64 %add22, i64 104) #7
  %i13 = bitcast i8* %call23 to %struct.node*
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  store %struct.node* %i13, %struct.node** %nodes, align 8
  %n24 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i14 = load i64, i64* %n24, align 8
  %call25 = call noalias i8* @calloc(i64 %i14, i64 64) #7
  %i15 = bitcast i8* %call25 to %struct.arc*
  %dummy_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  store %struct.arc* %i15, %struct.arc** %dummy_arcs, align 8
  %max_m26 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  %i16 = load i64, i64* %max_m26, align 8
  %call27 = call noalias i8* @calloc(i64 %i16, i64 64) #7
  %i17 = bitcast i8* %call27 to %struct.arc*
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  store %struct.arc* %i17, %struct.arc** %arcs, align 8
  %nodes28 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i18 = load %struct.node*, %struct.node** %nodes28, align 8
  %tobool = icmp ne %struct.node* %i18, null
  br i1 %tobool, label %land.lhs.true, label %if.then34

land.lhs.true:                                    ; preds = %if.end18
  %arcs29 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i19 = load %struct.arc*, %struct.arc** %arcs29, align 8
  %tobool30 = icmp ne %struct.arc* %i19, null
  br i1 %tobool30, label %land.lhs.true31, label %if.then34

land.lhs.true31:                                  ; preds = %land.lhs.true
  %dummy_arcs32 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  %i20 = load %struct.arc*, %struct.arc** %dummy_arcs32, align 8
  %tobool33 = icmp ne %struct.arc* %i20, null
  br i1 %tobool33, label %if.end37, label %if.then34

if.then34:                                        ; preds = %land.lhs.true31, %land.lhs.true, %if.end18
  %call35 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.2.27, i64 0, i64 0))
  %call36 = call i64 @getfree(%struct.network* %net)
  br label %return

if.end37:                                         ; preds = %land.lhs.true31
  %nodes38 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i21 = load %struct.node*, %struct.node** %nodes38, align 8
  %n39 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i22 = load i64, i64* %n39, align 8
  %add.ptr = getelementptr inbounds %struct.node, %struct.node* %i21, i64 %i22
  %add.ptr40 = getelementptr inbounds %struct.node, %struct.node* %add.ptr, i64 1
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  store %struct.node* %add.ptr40, %struct.node** %stop_nodes, align 8
  %arcs41 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i23 = load %struct.arc*, %struct.arc** %arcs41, align 8
  %m42 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i24 = load i64, i64* %m42, align 8
  %add.ptr43 = getelementptr inbounds %struct.arc, %struct.arc* %i23, i64 %i24
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  store %struct.arc* %add.ptr43, %struct.arc** %stop_arcs, align 8
  %dummy_arcs44 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  %i25 = load %struct.arc*, %struct.arc** %dummy_arcs44, align 8
  %n45 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i26 = load i64, i64* %n45, align 8
  %add.ptr46 = getelementptr inbounds %struct.arc, %struct.arc* %i25, i64 %i26
  %stop_dummy = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 26
  store %struct.arc* %add.ptr46, %struct.arc** %stop_dummy, align 8
  %nodes47 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i27 = load %struct.node*, %struct.node** %nodes47, align 8
  %arcs48 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i28 = load %struct.arc*, %struct.arc** %arcs48, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end37
  %i.0 = phi i64 [ 1, %if.end37 ], [ %inc, %for.inc ]
  %arc.0 = phi %struct.arc* [ %i28, %if.end37 ], [ %incdec.ptr129, %for.inc ]
  %n_trips49 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i29 = load i64, i64* %n_trips49, align 8
  %cmp50 = icmp sle i64 %i.0, %i29
  br i1 %cmp50, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %arraydecay51 = getelementptr inbounds [201 x i8], [201 x i8]* %instring, i64 0, i64 0
  %call52 = call i8* @fgets(i8* %arraydecay51, i32 200, %struct._IO_FILE* %call)
  %arraydecay53 = getelementptr inbounds [201 x i8], [201 x i8]* %instring, i64 0, i64 0
  %call54 = call i32 (i8*, i8*, ...) @__isoc99_sscanf(i8* %arraydecay53, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.1.26, i64 0, i64 0), i64* %t, i64* %h) #7
  %cmp55 = icmp ne i32 %call54, 2
  br i1 %cmp55, label %if.then57, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %for.body
  %i30 = load i64, i64* %t, align 8
  %i31 = load i64, i64* %h, align 8
  %cmp56 = icmp sgt i64 %i30, %i31
  br i1 %cmp56, label %if.then57, label %if.end58

if.then57:                                        ; preds = %lor.lhs.false, %for.body
  br label %return

if.end58:                                         ; preds = %lor.lhs.false
  %sub59 = sub nsw i64 0, %i.0
  %conv = trunc i64 %sub59 to i32
  %arrayidx = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i.0
  %number = getelementptr inbounds %struct.node, %struct.node* %arrayidx, i32 0, i32 12
  store i32 %conv, i32* %number, align 8
  %arrayidx60 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i.0
  %flow = getelementptr inbounds %struct.node, %struct.node* %arrayidx60, i32 0, i32 10
  store i64 -1, i64* %flow, align 8
  %conv61 = trunc i64 %i.0 to i32
  %n_trips62 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i32 = load i64, i64* %n_trips62, align 8
  %add63 = add nsw i64 %i.0, %i32
  %arrayidx64 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %add63
  %number65 = getelementptr inbounds %struct.node, %struct.node* %arrayidx64, i32 0, i32 12
  store i32 %conv61, i32* %number65, align 8
  %n_trips66 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i33 = load i64, i64* %n_trips66, align 8
  %add67 = add nsw i64 %i.0, %i33
  %arrayidx68 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %add67
  %flow69 = getelementptr inbounds %struct.node, %struct.node* %arrayidx68, i32 0, i32 10
  store i64 1, i64* %flow69, align 8
  %i34 = load i64, i64* %t, align 8
  %conv70 = trunc i64 %i34 to i32
  %arrayidx71 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i.0
  %time = getelementptr inbounds %struct.node, %struct.node* %arrayidx71, i32 0, i32 13
  store i32 %conv70, i32* %time, align 4
  %i35 = load i64, i64* %h, align 8
  %conv72 = trunc i64 %i35 to i32
  %n_trips73 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i36 = load i64, i64* %n_trips73, align 8
  %add74 = add nsw i64 %i.0, %i36
  %arrayidx75 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %add74
  %time76 = getelementptr inbounds %struct.node, %struct.node* %arrayidx75, i32 0, i32 13
  store i32 %conv72, i32* %time76, align 4
  %n77 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i37 = load i64, i64* %n77, align 8
  %arrayidx78 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i37
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  store %struct.node* %arrayidx78, %struct.node** %tail, align 8
  %arrayidx79 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i.0
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  store %struct.node* %arrayidx79, %struct.node** %head, align 8
  %bigM = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i38 = load i64, i64* %bigM, align 8
  %add80 = add nsw i64 %i38, 15
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 0
  store i64 %add80, i64* %cost, align 8
  %org_cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 7
  store i64 %add80, i64* %org_cost, align 8
  %tail81 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i39 = load %struct.node*, %struct.node** %tail81, align 8
  %firstout = getelementptr inbounds %struct.node, %struct.node* %i39, i32 0, i32 7
  %i40 = load %struct.arc*, %struct.arc** %firstout, align 8
  %nextout = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 4
  store %struct.arc* %i40, %struct.arc** %nextout, align 8
  %tail82 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i41 = load %struct.node*, %struct.node** %tail82, align 8
  %firstout83 = getelementptr inbounds %struct.node, %struct.node* %i41, i32 0, i32 7
  store %struct.arc* %arc.0, %struct.arc** %firstout83, align 8
  %head84 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i42 = load %struct.node*, %struct.node** %head84, align 8
  %firstin = getelementptr inbounds %struct.node, %struct.node* %i42, i32 0, i32 8
  %i43 = load %struct.arc*, %struct.arc** %firstin, align 8
  %nextin = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 5
  store %struct.arc* %i43, %struct.arc** %nextin, align 8
  %head85 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i44 = load %struct.node*, %struct.node** %head85, align 8
  %firstin86 = getelementptr inbounds %struct.node, %struct.node* %i44, i32 0, i32 8
  store %struct.arc* %arc.0, %struct.arc** %firstin86, align 8
  %incdec.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  %n_trips87 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i45 = load i64, i64* %n_trips87, align 8
  %add88 = add nsw i64 %i.0, %i45
  %arrayidx89 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %add88
  %tail90 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 1
  store %struct.node* %arrayidx89, %struct.node** %tail90, align 8
  %n91 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i46 = load i64, i64* %n91, align 8
  %arrayidx92 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i46
  %head93 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 2
  store %struct.node* %arrayidx92, %struct.node** %head93, align 8
  %cost94 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 0
  store i64 15, i64* %cost94, align 8
  %org_cost95 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 7
  store i64 15, i64* %org_cost95, align 8
  %tail96 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 1
  %i47 = load %struct.node*, %struct.node** %tail96, align 8
  %firstout97 = getelementptr inbounds %struct.node, %struct.node* %i47, i32 0, i32 7
  %i48 = load %struct.arc*, %struct.arc** %firstout97, align 8
  %nextout98 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 4
  store %struct.arc* %i48, %struct.arc** %nextout98, align 8
  %tail99 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 1
  %i49 = load %struct.node*, %struct.node** %tail99, align 8
  %firstout100 = getelementptr inbounds %struct.node, %struct.node* %i49, i32 0, i32 7
  store %struct.arc* %incdec.ptr, %struct.arc** %firstout100, align 8
  %head101 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 2
  %i50 = load %struct.node*, %struct.node** %head101, align 8
  %firstin102 = getelementptr inbounds %struct.node, %struct.node* %i50, i32 0, i32 8
  %i51 = load %struct.arc*, %struct.arc** %firstin102, align 8
  %nextin103 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 5
  store %struct.arc* %i51, %struct.arc** %nextin103, align 8
  %head104 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 0, i32 2
  %i52 = load %struct.node*, %struct.node** %head104, align 8
  %firstin105 = getelementptr inbounds %struct.node, %struct.node* %i52, i32 0, i32 8
  store %struct.arc* %incdec.ptr, %struct.arc** %firstin105, align 8
  %incdec.ptr106 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr, i32 1
  %arrayidx107 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i.0
  %tail108 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 1
  store %struct.node* %arrayidx107, %struct.node** %tail108, align 8
  %n_trips109 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i53 = load i64, i64* %n_trips109, align 8
  %add110 = add nsw i64 %i.0, %i53
  %arrayidx111 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %add110
  %head112 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 2
  store %struct.node* %arrayidx111, %struct.node** %head112, align 8
  %bigM113 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i54 = load i64, i64* %bigM113, align 8
  %cmp114 = icmp sgt i64 %i54, 10000000
  br i1 %cmp114, label %cond.true, label %cond.false

cond.true:                                        ; preds = %if.end58
  %bigM116 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i55 = load i64, i64* %bigM116, align 8
  br label %cond.end

cond.false:                                       ; preds = %if.end58
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i64 [ %i55, %cond.true ], [ 10000000, %cond.false ]
  %mul = mul nsw i64 2, %cond
  %cost117 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 0
  store i64 %mul, i64* %cost117, align 8
  %org_cost118 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 7
  store i64 %mul, i64* %org_cost118, align 8
  %tail119 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 1
  %i56 = load %struct.node*, %struct.node** %tail119, align 8
  %firstout120 = getelementptr inbounds %struct.node, %struct.node* %i56, i32 0, i32 7
  %i57 = load %struct.arc*, %struct.arc** %firstout120, align 8
  %nextout121 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 4
  store %struct.arc* %i57, %struct.arc** %nextout121, align 8
  %tail122 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 1
  %i58 = load %struct.node*, %struct.node** %tail122, align 8
  %firstout123 = getelementptr inbounds %struct.node, %struct.node* %i58, i32 0, i32 7
  store %struct.arc* %incdec.ptr106, %struct.arc** %firstout123, align 8
  %head124 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 2
  %i59 = load %struct.node*, %struct.node** %head124, align 8
  %firstin125 = getelementptr inbounds %struct.node, %struct.node* %i59, i32 0, i32 8
  %i60 = load %struct.arc*, %struct.arc** %firstin125, align 8
  %nextin126 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 5
  store %struct.arc* %i60, %struct.arc** %nextin126, align 8
  %head127 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 0, i32 2
  %i61 = load %struct.node*, %struct.node** %head127, align 8
  %firstin128 = getelementptr inbounds %struct.node, %struct.node* %i61, i32 0, i32 8
  store %struct.arc* %incdec.ptr106, %struct.arc** %firstin128, align 8
  %incdec.ptr129 = getelementptr inbounds %struct.arc, %struct.arc* %incdec.ptr106, i32 1
  br label %for.inc

for.inc:                                          ; preds = %cond.end
  %inc = add nsw i64 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %n_trips130 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i62 = load i64, i64* %n_trips130, align 8
  %add131 = add nsw i64 %i62, 1
  %cmp132 = icmp ne i64 %i.0, %add131
  br i1 %cmp132, label %if.then134, label %if.end135

if.then134:                                       ; preds = %for.end
  br label %return

if.end135:                                        ; preds = %for.end
  br label %for.cond136

for.cond136:                                      ; preds = %for.inc167, %if.end135
  %i.1 = phi i64 [ 0, %if.end135 ], [ %inc168, %for.inc167 ]
  %arc.1 = phi %struct.arc* [ %arc.0, %if.end135 ], [ %incdec.ptr169, %for.inc167 ]
  %m_org137 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 6
  %i63 = load i64, i64* %m_org137, align 8
  %cmp138 = icmp slt i64 %i.1, %i63
  br i1 %cmp138, label %for.body140, label %for.end170

for.body140:                                      ; preds = %for.cond136
  %arraydecay141 = getelementptr inbounds [201 x i8], [201 x i8]* %instring, i64 0, i64 0
  %call142 = call i8* @fgets(i8* %arraydecay141, i32 200, %struct._IO_FILE* %call)
  %arraydecay143 = getelementptr inbounds [201 x i8], [201 x i8]* %instring, i64 0, i64 0
  %call144 = call i32 (i8*, i8*, ...) @__isoc99_sscanf(i8* %arraydecay143, i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str.3.28, i64 0, i64 0), i64* %t, i64* %h, i64* %c) #7
  %cmp145 = icmp ne i32 %call144, 3
  br i1 %cmp145, label %if.then147, label %if.end148

if.then147:                                       ; preds = %for.body140
  br label %return

if.end148:                                        ; preds = %for.body140
  %i64 = load i64, i64* %t, align 8
  %n_trips149 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i65 = load i64, i64* %n_trips149, align 8
  %add150 = add nsw i64 %i64, %i65
  %arrayidx151 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %add150
  %tail152 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  store %struct.node* %arrayidx151, %struct.node** %tail152, align 8
  %i66 = load i64, i64* %h, align 8
  %arrayidx153 = getelementptr inbounds %struct.node, %struct.node* %i27, i64 %i66
  %head154 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 2
  store %struct.node* %arrayidx153, %struct.node** %head154, align 8
  %i67 = load i64, i64* %c, align 8
  %org_cost155 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 7
  store i64 %i67, i64* %org_cost155, align 8
  %i68 = load i64, i64* %c, align 8
  %cost156 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 0
  store i64 %i68, i64* %cost156, align 8
  %tail157 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  %i69 = load %struct.node*, %struct.node** %tail157, align 8
  %firstout158 = getelementptr inbounds %struct.node, %struct.node* %i69, i32 0, i32 7
  %i70 = load %struct.arc*, %struct.arc** %firstout158, align 8
  %nextout159 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 4
  store %struct.arc* %i70, %struct.arc** %nextout159, align 8
  %tail160 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  %i71 = load %struct.node*, %struct.node** %tail160, align 8
  %firstout161 = getelementptr inbounds %struct.node, %struct.node* %i71, i32 0, i32 7
  store %struct.arc* %arc.1, %struct.arc** %firstout161, align 8
  %head162 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 2
  %i72 = load %struct.node*, %struct.node** %head162, align 8
  %firstin163 = getelementptr inbounds %struct.node, %struct.node* %i72, i32 0, i32 8
  %i73 = load %struct.arc*, %struct.arc** %firstin163, align 8
  %nextin164 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 5
  store %struct.arc* %i73, %struct.arc** %nextin164, align 8
  %head165 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 2
  %i74 = load %struct.node*, %struct.node** %head165, align 8
  %firstin166 = getelementptr inbounds %struct.node, %struct.node* %i74, i32 0, i32 8
  store %struct.arc* %arc.1, %struct.arc** %firstin166, align 8
  br label %for.inc167

for.inc167:                                       ; preds = %if.end148
  %inc168 = add nsw i64 %i.1, 1
  %incdec.ptr169 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 1
  br label %for.cond136

for.end170:                                       ; preds = %for.cond136
  %stop_arcs171 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i75 = load %struct.arc*, %struct.arc** %stop_arcs171, align 8
  %cmp172 = icmp ne %struct.arc* %i75, %arc.1
  br i1 %cmp172, label %if.then174, label %if.end190

if.then174:                                       ; preds = %for.end170
  %stop_arcs175 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  store %struct.arc* %arc.1, %struct.arc** %stop_arcs175, align 8
  %arcs176 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i76 = load %struct.arc*, %struct.arc** %arcs176, align 8
  %m177 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  store i64 0, i64* %m177, align 8
  br label %for.cond178

for.cond178:                                      ; preds = %for.inc185, %if.then174
  %arc.2 = phi %struct.arc* [ %i76, %if.then174 ], [ %incdec.ptr186, %for.inc185 ]
  %stop_arcs179 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i77 = load %struct.arc*, %struct.arc** %stop_arcs179, align 8
  %cmp180 = icmp ult %struct.arc* %arc.2, %i77
  br i1 %cmp180, label %for.body182, label %for.end187

for.body182:                                      ; preds = %for.cond178
  %m183 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i78 = load i64, i64* %m183, align 8
  %inc184 = add nsw i64 %i78, 1
  store i64 %inc184, i64* %m183, align 8
  br label %for.inc185

for.inc185:                                       ; preds = %for.body182
  %incdec.ptr186 = getelementptr inbounds %struct.arc, %struct.arc* %arc.2, i32 1
  br label %for.cond178

for.end187:                                       ; preds = %for.cond178
  %m188 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i79 = load i64, i64* %m188, align 8
  %m_org189 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 6
  store i64 %i79, i64* %m_org189, align 8
  br label %if.end190

if.end190:                                        ; preds = %for.end187, %for.end170
  %call191 = call i32 @fclose(%struct._IO_FILE* %call)
  %clustfile = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 1
  %arrayidx192 = getelementptr inbounds [200 x i8], [200 x i8]* %clustfile, i64 0, i64 0
  store i8 0, i8* %arrayidx192, align 8
  br label %for.cond193

for.cond193:                                      ; preds = %for.inc226, %if.end190
  %i.2 = phi i64 [ 1, %if.end190 ], [ %inc227, %for.inc226 ]
  %n_trips194 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i80 = load i64, i64* %n_trips194, align 8
  %cmp195 = icmp sle i64 %i.2, %i80
  br i1 %cmp195, label %for.body197, label %for.end228

for.body197:                                      ; preds = %for.cond193
  %bigM198 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i81 = load i64, i64* %bigM198, align 8
  %cmp199 = icmp sgt i64 %i81, 10000000
  br i1 %cmp199, label %cond.true201, label %cond.false203

cond.true201:                                     ; preds = %for.body197
  %bigM202 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i82 = load i64, i64* %bigM202, align 8
  br label %cond.end204

cond.false203:                                    ; preds = %for.body197
  br label %cond.end204

cond.end204:                                      ; preds = %cond.false203, %cond.true201
  %cond205 = phi i64 [ %i82, %cond.true201 ], [ 10000000, %cond.false203 ]
  %mul206 = mul nsw i64 -2, %cond205
  %arcs207 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i83 = load %struct.arc*, %struct.arc** %arcs207, align 8
  %mul208 = mul nsw i64 3, %i.2
  %sub209 = sub nsw i64 %mul208, 1
  %arrayidx210 = getelementptr inbounds %struct.arc, %struct.arc* %i83, i64 %sub209
  %cost211 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx210, i32 0, i32 0
  store i64 %mul206, i64* %cost211, align 8
  %bigM212 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i84 = load i64, i64* %bigM212, align 8
  %cmp213 = icmp sgt i64 %i84, 10000000
  br i1 %cmp213, label %cond.true215, label %cond.false217

cond.true215:                                     ; preds = %cond.end204
  %bigM216 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i85 = load i64, i64* %bigM216, align 8
  br label %cond.end218

cond.false217:                                    ; preds = %cond.end204
  br label %cond.end218

cond.end218:                                      ; preds = %cond.false217, %cond.true215
  %cond219 = phi i64 [ %i85, %cond.true215 ], [ 10000000, %cond.false217 ]
  %mul220 = mul nsw i64 -2, %cond219
  %arcs221 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i86 = load %struct.arc*, %struct.arc** %arcs221, align 8
  %mul222 = mul nsw i64 3, %i.2
  %sub223 = sub nsw i64 %mul222, 1
  %arrayidx224 = getelementptr inbounds %struct.arc, %struct.arc* %i86, i64 %sub223
  %org_cost225 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx224, i32 0, i32 7
  store i64 %mul220, i64* %org_cost225, align 8
  br label %for.inc226

for.inc226:                                       ; preds = %cond.end218
  %inc227 = add nsw i64 %i.2, 1
  br label %for.cond193

for.end228:                                       ; preds = %for.cond193
  br label %return

return:                                           ; preds = %for.end228, %if.then147, %if.then134, %if.then57, %if.then34, %if.then6, %if.then
  %retval.0 = phi i64 [ -1, %if.then ], [ -1, %if.then6 ], [ -1, %if.then57 ], [ -1, %if.then134 ], [ -1, %if.then147 ], [ 0, %for.end228 ], [ -1, %if.then34 ]
  ret i64 %retval.0
}

declare dso_local noalias %struct._IO_FILE* @fopen(i8*, i8*) #1

declare dso_local i8* @fgets(i8*, i32, %struct._IO_FILE*) #1

; Function Attrs: nounwind
declare dso_local i32 @__isoc99_sscanf(i8*, i8*, ...) #4

; Function Attrs: nounwind
declare dso_local noalias i8* @calloc(i64, i64) #4

declare dso_local i32 @fclose(%struct._IO_FILE*) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @resize_prob(%struct.network* %net) #0 {
entry:
  %max_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 9
  %i = load i64, i64* %max_new_m, align 8
  %max_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  %i1 = load i64, i64* %max_m, align 8
  %add = add nsw i64 %i1, %i
  store i64 %add, i64* %max_m, align 8
  %max_new_m1 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 9
  %i2 = load i64, i64* %max_new_m1, align 8
  %max_residual_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  %i3 = load i64, i64* %max_residual_new_m, align 8
  %add2 = add nsw i64 %i3, %i2
  store i64 %add2, i64* %max_residual_new_m, align 8
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i4 = load %struct.arc*, %struct.arc** %arcs, align 8
  %i5 = bitcast %struct.arc* %i4 to i8*
  %max_m3 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  %i6 = load i64, i64* %max_m3, align 8
  %mul = mul i64 %i6, 64
  %call = call i8* @realloc(i8* %i5, i64 %mul) #7
  %i7 = bitcast i8* %call to %struct.arc*
  %tobool = icmp ne %struct.arc* %i7, null
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  %inputfile = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 0
  %arraydecay = getelementptr inbounds [200 x i8], [200 x i8]* %inputfile, i64 0, i64 0
  %call4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.29, i64 0, i64 0), i8* %arraydecay)
  %i8 = load %struct._IO_FILE*, %struct._IO_FILE** @stdout, align 8
  %call5 = call i32 @fflush(%struct._IO_FILE* %i8)
  br label %return

if.end:                                           ; preds = %entry
  %i9 = ptrtoint %struct.arc* %i7 to i64
  %arcs6 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i10 = load %struct.arc*, %struct.arc** %arcs6, align 8
  %i11 = ptrtoint %struct.arc* %i10 to i64
  %sub = sub i64 %i9, %i11
  %arcs7 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  store %struct.arc* %i7, %struct.arc** %arcs7, align 8
  %m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i12 = load i64, i64* %m, align 8
  %add.ptr = getelementptr inbounds %struct.arc, %struct.arc* %i7, i64 %i12
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  store %struct.arc* %add.ptr, %struct.arc** %stop_arcs, align 8
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i13 = load %struct.node*, %struct.node** %nodes, align 8
  %incdec.ptr = getelementptr inbounds %struct.node, %struct.node* %i13, i32 1
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  %i14 = load %struct.node*, %struct.node** %stop_nodes, align 8
  %i15 = bitcast %struct.node* %i14 to i8*
  %i16 = bitcast i8* %i15 to %struct.node*
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end
  %node.0 = phi %struct.node* [ %incdec.ptr, %if.end ], [ %incdec.ptr13, %for.inc ]
  %cmp = icmp ult %struct.node* %node.0, %i16
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %pred = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 3
  %i17 = load %struct.node*, %struct.node** %pred, align 8
  %cmp8 = icmp ne %struct.node* %i17, %i13
  br i1 %cmp8, label %if.then9, label %if.end12

if.then9:                                         ; preds = %for.body
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 6
  %i18 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %i19 = ptrtoint %struct.arc* %i18 to i64
  %add10 = add i64 %i19, %sub
  %i20 = inttoptr i64 %add10 to %struct.arc*
  %basic_arc11 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 6
  store %struct.arc* %i20, %struct.arc** %basic_arc11, align 8
  br label %if.end12

if.end12:                                         ; preds = %if.then9, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end12
  %incdec.ptr13 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %return

return:                                           ; preds = %for.end, %if.then
  %retval.0 = phi i64 [ 0, %for.end ], [ -1, %if.then ]
  ret i64 %retval.0
}

; Function Attrs: nounwind
declare dso_local i8* @realloc(i8*, i64) #4

declare dso_local i32 @fflush(%struct._IO_FILE*) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @insert_new_arc(%struct.arc* %new, i64 %newpos, %struct.node* %tail, %struct.node* %head, i64 %cost, i64 %red_cost) #0 {
entry:
  %arrayidx = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %newpos
  %tail1 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx, i32 0, i32 1
  store %struct.node* %tail, %struct.node** %tail1, align 8
  %arrayidx2 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %newpos
  %head3 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx2, i32 0, i32 2
  store %struct.node* %head, %struct.node** %head3, align 8
  %arrayidx4 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %newpos
  %org_cost = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx4, i32 0, i32 7
  store i64 %cost, i64* %org_cost, align 8
  %arrayidx5 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %newpos
  %cost6 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx5, i32 0, i32 0
  store i64 %cost, i64* %cost6, align 8
  %arrayidx7 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %newpos
  %flow = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx7, i32 0, i32 6
  store i64 %red_cost, i64* %flow, align 8
  %add = add nsw i64 %newpos, 1
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %pos.0 = phi i64 [ %add, %entry ], [ %div46, %while.body ]
  %sub = sub nsw i64 %pos.0, 1
  %tobool = icmp ne i64 %sub, 0
  br i1 %tobool, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %while.cond
  %div = sdiv i64 %pos.0, 2
  %sub8 = sub nsw i64 %div, 1
  %arrayidx9 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub8
  %flow10 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx9, i32 0, i32 6
  %i = load i64, i64* %flow10, align 8
  %cmp = icmp sgt i64 %red_cost, %i
  br label %land.end

land.end:                                         ; preds = %land.rhs, %while.cond
  %i1 = phi i1 [ false, %while.cond ], [ %cmp, %land.rhs ]
  br i1 %i1, label %while.body, label %while.end

while.body:                                       ; preds = %land.end
  %div11 = sdiv i64 %pos.0, 2
  %sub12 = sub nsw i64 %div11, 1
  %arrayidx13 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub12
  %tail14 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx13, i32 0, i32 1
  %i2 = load %struct.node*, %struct.node** %tail14, align 8
  %sub15 = sub nsw i64 %pos.0, 1
  %arrayidx16 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub15
  %tail17 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx16, i32 0, i32 1
  store %struct.node* %i2, %struct.node** %tail17, align 8
  %div18 = sdiv i64 %pos.0, 2
  %sub19 = sub nsw i64 %div18, 1
  %arrayidx20 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub19
  %head21 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx20, i32 0, i32 2
  %i3 = load %struct.node*, %struct.node** %head21, align 8
  %sub22 = sub nsw i64 %pos.0, 1
  %arrayidx23 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub22
  %head24 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx23, i32 0, i32 2
  store %struct.node* %i3, %struct.node** %head24, align 8
  %div25 = sdiv i64 %pos.0, 2
  %sub26 = sub nsw i64 %div25, 1
  %arrayidx27 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub26
  %cost28 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx27, i32 0, i32 0
  %i4 = load i64, i64* %cost28, align 8
  %sub29 = sub nsw i64 %pos.0, 1
  %arrayidx30 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub29
  %cost31 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx30, i32 0, i32 0
  store i64 %i4, i64* %cost31, align 8
  %div32 = sdiv i64 %pos.0, 2
  %sub33 = sub nsw i64 %div32, 1
  %arrayidx34 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub33
  %cost35 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx34, i32 0, i32 0
  %i5 = load i64, i64* %cost35, align 8
  %sub36 = sub nsw i64 %pos.0, 1
  %arrayidx37 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub36
  %org_cost38 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx37, i32 0, i32 7
  store i64 %i5, i64* %org_cost38, align 8
  %div39 = sdiv i64 %pos.0, 2
  %sub40 = sub nsw i64 %div39, 1
  %arrayidx41 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub40
  %flow42 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx41, i32 0, i32 6
  %i6 = load i64, i64* %flow42, align 8
  %sub43 = sub nsw i64 %pos.0, 1
  %arrayidx44 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub43
  %flow45 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx44, i32 0, i32 6
  store i64 %i6, i64* %flow45, align 8
  %div46 = sdiv i64 %pos.0, 2
  %sub47 = sub nsw i64 %div46, 1
  %arrayidx48 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub47
  %tail49 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx48, i32 0, i32 1
  store %struct.node* %tail, %struct.node** %tail49, align 8
  %sub50 = sub nsw i64 %div46, 1
  %arrayidx51 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub50
  %head52 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx51, i32 0, i32 2
  store %struct.node* %head, %struct.node** %head52, align 8
  %sub53 = sub nsw i64 %div46, 1
  %arrayidx54 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub53
  %cost55 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx54, i32 0, i32 0
  store i64 %cost, i64* %cost55, align 8
  %sub56 = sub nsw i64 %div46, 1
  %arrayidx57 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub56
  %org_cost58 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx57, i32 0, i32 7
  store i64 %cost, i64* %org_cost58, align 8
  %sub59 = sub nsw i64 %div46, 1
  %arrayidx60 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub59
  %flow61 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx60, i32 0, i32 6
  store i64 %red_cost, i64* %flow61, align 8
  br label %while.cond

while.end:                                        ; preds = %land.end
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @replace_weaker_arc(%struct.network* %net, %struct.arc* %new, %struct.node* %tail, %struct.node* %head, i64 %cost, i64 %red_cost) #0 {
entry:
  %arrayidx = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 0
  %tail1 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx, i32 0, i32 1
  store %struct.node* %tail, %struct.node** %tail1, align 8
  %arrayidx2 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 0
  %head3 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx2, i32 0, i32 2
  store %struct.node* %head, %struct.node** %head3, align 8
  %arrayidx4 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 0
  %org_cost = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx4, i32 0, i32 7
  store i64 %cost, i64* %org_cost, align 8
  %arrayidx5 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 0
  %cost6 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx5, i32 0, i32 0
  store i64 %cost, i64* %cost6, align 8
  %arrayidx7 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 0
  %flow = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx7, i32 0, i32 6
  store i64 %red_cost, i64* %flow, align 8
  %arrayidx8 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 1
  %flow9 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx8, i32 0, i32 6
  %i = load i64, i64* %flow9, align 8
  %arrayidx10 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 2
  %flow11 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx10, i32 0, i32 6
  %i1 = load i64, i64* %flow11, align 8
  %cmp12 = icmp sgt i64 %i, %i1
  %i2 = zext i1 %cmp12 to i64
  %cond = select i1 %cmp12, i32 2, i32 3
  %conv = sext i32 %cond to i64
  br label %while.cond

while.cond:                                       ; preds = %if.end75, %entry
  %pos.0 = phi i64 [ 1, %entry ], [ %cmp.0, %if.end75 ]
  %cmp.0 = phi i64 [ %conv, %entry ], [ %cmp.2, %if.end75 ]
  %max_residual_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  %i3 = load i64, i64* %max_residual_new_m, align 8
  %cmp13 = icmp sle i64 %cmp.0, %i3
  br i1 %cmp13, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %while.cond
  %sub = sub nsw i64 %cmp.0, 1
  %arrayidx15 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub
  %flow16 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx15, i32 0, i32 6
  %i4 = load i64, i64* %flow16, align 8
  %cmp17 = icmp slt i64 %red_cost, %i4
  br label %land.end

land.end:                                         ; preds = %land.rhs, %while.cond
  %i5 = phi i1 [ false, %while.cond ], [ %cmp17, %land.rhs ]
  br i1 %i5, label %while.body, label %while.end

while.body:                                       ; preds = %land.end
  %sub19 = sub nsw i64 %cmp.0, 1
  %arrayidx20 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub19
  %tail21 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx20, i32 0, i32 1
  %i6 = load %struct.node*, %struct.node** %tail21, align 8
  %sub22 = sub nsw i64 %pos.0, 1
  %arrayidx23 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub22
  %tail24 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx23, i32 0, i32 1
  store %struct.node* %i6, %struct.node** %tail24, align 8
  %sub25 = sub nsw i64 %cmp.0, 1
  %arrayidx26 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub25
  %head27 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx26, i32 0, i32 2
  %i7 = load %struct.node*, %struct.node** %head27, align 8
  %sub28 = sub nsw i64 %pos.0, 1
  %arrayidx29 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub28
  %head30 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx29, i32 0, i32 2
  store %struct.node* %i7, %struct.node** %head30, align 8
  %sub31 = sub nsw i64 %cmp.0, 1
  %arrayidx32 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub31
  %cost33 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx32, i32 0, i32 0
  %i8 = load i64, i64* %cost33, align 8
  %sub34 = sub nsw i64 %pos.0, 1
  %arrayidx35 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub34
  %cost36 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx35, i32 0, i32 0
  store i64 %i8, i64* %cost36, align 8
  %sub37 = sub nsw i64 %cmp.0, 1
  %arrayidx38 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub37
  %cost39 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx38, i32 0, i32 0
  %i9 = load i64, i64* %cost39, align 8
  %sub40 = sub nsw i64 %pos.0, 1
  %arrayidx41 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub40
  %org_cost42 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx41, i32 0, i32 7
  store i64 %i9, i64* %org_cost42, align 8
  %sub43 = sub nsw i64 %cmp.0, 1
  %arrayidx44 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub43
  %flow45 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx44, i32 0, i32 6
  %i10 = load i64, i64* %flow45, align 8
  %sub46 = sub nsw i64 %pos.0, 1
  %arrayidx47 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub46
  %flow48 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx47, i32 0, i32 6
  store i64 %i10, i64* %flow48, align 8
  %sub49 = sub nsw i64 %cmp.0, 1
  %arrayidx50 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub49
  %tail51 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx50, i32 0, i32 1
  store %struct.node* %tail, %struct.node** %tail51, align 8
  %sub52 = sub nsw i64 %cmp.0, 1
  %arrayidx53 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub52
  %head54 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx53, i32 0, i32 2
  store %struct.node* %head, %struct.node** %head54, align 8
  %sub55 = sub nsw i64 %cmp.0, 1
  %arrayidx56 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub55
  %cost57 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx56, i32 0, i32 0
  store i64 %cost, i64* %cost57, align 8
  %sub58 = sub nsw i64 %cmp.0, 1
  %arrayidx59 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub58
  %org_cost60 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx59, i32 0, i32 7
  store i64 %cost, i64* %org_cost60, align 8
  %sub61 = sub nsw i64 %cmp.0, 1
  %arrayidx62 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub61
  %flow63 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx62, i32 0, i32 6
  store i64 %red_cost, i64* %flow63, align 8
  %mul = mul nsw i64 %cmp.0, 2
  %add = add nsw i64 %mul, 1
  %max_residual_new_m64 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  %i11 = load i64, i64* %max_residual_new_m64, align 8
  %cmp65 = icmp sle i64 %add, %i11
  br i1 %cmp65, label %if.then, label %if.end75

if.then:                                          ; preds = %while.body
  %sub67 = sub nsw i64 %mul, 1
  %arrayidx68 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %sub67
  %flow69 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx68, i32 0, i32 6
  %i12 = load i64, i64* %flow69, align 8
  %arrayidx70 = getelementptr inbounds %struct.arc, %struct.arc* %new, i64 %mul
  %flow71 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx70, i32 0, i32 6
  %i13 = load i64, i64* %flow71, align 8
  %cmp72 = icmp slt i64 %i12, %i13
  br i1 %cmp72, label %if.then74, label %if.end

if.then74:                                        ; preds = %if.then
  %inc = add nsw i64 %mul, 1
  br label %if.end

if.end:                                           ; preds = %if.then74, %if.then
  %cmp.1 = phi i64 [ %inc, %if.then74 ], [ %mul, %if.then ]
  br label %if.end75

if.end75:                                         ; preds = %if.end, %while.body
  %cmp.2 = phi i64 [ %cmp.1, %if.end ], [ %mul, %while.body ]
  br label %while.cond

while.end:                                        ; preds = %land.end
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @price_out_impl(%struct.network* %net) #0 {
entry:
  %bigM1 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 18
  %i = load i64, i64* %bigM1, align 8
  %sub = sub nsw i64 %i, 15
  %n_trips = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i1 = load i64, i64* %n_trips, align 8
  %cmp = icmp sle i64 %i1, 15000
  br i1 %cmp, label %if.then, label %if.end12

if.then:                                          ; preds = %entry
  %m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i2 = load i64, i64* %m, align 8
  %max_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 9
  %i3 = load i64, i64* %max_new_m, align 8
  %add = add nsw i64 %i2, %i3
  %max_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  %i4 = load i64, i64* %max_m, align 8
  %cmp2 = icmp sgt i64 %add, %i4
  br i1 %cmp2, label %land.lhs.true, label %if.end11

land.lhs.true:                                    ; preds = %if.then
  %n_trips3 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i5 = load i64, i64* %n_trips3, align 8
  %n_trips4 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i6 = load i64, i64* %n_trips4, align 8
  %mul = mul nsw i64 %i5, %i6
  %div = sdiv i64 %mul, 2
  %m5 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i7 = load i64, i64* %m5, align 8
  %add6 = add nsw i64 %div, %i7
  %max_m7 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 4
  %i8 = load i64, i64* %max_m7, align 8
  %cmp8 = icmp sgt i64 %add6, %i8
  br i1 %cmp8, label %if.then9, label %if.end11

if.then9:                                         ; preds = %land.lhs.true
  %call = call i64 @resize_prob(%struct.network* %net)
  %tobool = icmp ne i64 %call, 0
  br i1 %tobool, label %if.then10, label %if.end

if.then10:                                        ; preds = %if.then9
  br label %return

if.end:                                           ; preds = %if.then9
  call void @refresh_neighbour_lists(%struct.network* %net)
  br label %if.end11

if.end11:                                         ; preds = %if.end, %land.lhs.true, %if.then
  %resized.0 = phi i64 [ 1, %if.end ], [ 0, %land.lhs.true ], [ 0, %if.then ]
  br label %if.end12

if.end12:                                         ; preds = %if.end11, %entry
  %resized.1 = phi i64 [ %resized.0, %if.end11 ], [ 0, %entry ]
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i9 = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %n_trips13 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i10 = load i64, i64* %n_trips13, align 8
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i11 = load %struct.arc*, %struct.arc** %arcs, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.end12
  %arcout.0 = phi %struct.arc* [ %i11, %if.end12 ], [ %add.ptr, %for.inc ]
  %i.0 = phi i64 [ 0, %if.end12 ], [ %inc, %for.inc ]
  %cmp14 = icmp slt i64 %i.0, %i10
  br i1 %cmp14, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %for.cond
  %arrayidx = getelementptr inbounds %struct.arc, %struct.arc* %arcout.0, i64 1
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx, i32 0, i32 3
  %i12 = load i32, i32* %ident, align 8
  %cmp15 = icmp eq i32 %i12, -1
  br label %land.end

land.end:                                         ; preds = %land.rhs, %for.cond
  %i13 = phi i1 [ false, %for.cond ], [ %cmp15, %land.rhs ]
  br i1 %i13, label %for.body, label %for.end

for.body:                                         ; preds = %land.end
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i64 %i.0, 1
  %add.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arcout.0, i64 3
  br label %for.cond

for.end:                                          ; preds = %land.end
  br label %for.cond16

for.cond16:                                       ; preds = %for.inc66, %for.end
  %arcout.1 = phi %struct.arc* [ %arcout.0, %for.end ], [ %add.ptr68, %for.inc66 ]
  %new_arcs.0 = phi i64 [ 0, %for.end ], [ %new_arcs.4, %for.inc66 ]
  %i.1 = phi i64 [ %i.0, %for.end ], [ %inc67, %for.inc66 ]
  %first_of_sparse_list.0 = phi %struct.arc* [ null, %for.end ], [ %first_of_sparse_list.1, %for.inc66 ]
  %cmp17 = icmp slt i64 %i.1, %i10
  br i1 %cmp17, label %for.body18, label %for.end69

for.body18:                                       ; preds = %for.cond16
  %arrayidx19 = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i64 1
  %ident20 = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx19, i32 0, i32 3
  %i14 = load i32, i32* %ident20, align 8
  %cmp21 = icmp ne i32 %i14, -1
  br i1 %cmp21, label %if.then22, label %if.end26

if.then22:                                        ; preds = %for.body18
  %head23 = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i32 0, i32 2
  %i15 = load %struct.node*, %struct.node** %head23, align 8
  %firstout = getelementptr inbounds %struct.node, %struct.node* %i15, i32 0, i32 7
  %i16 = load %struct.arc*, %struct.arc** %firstout, align 8
  %head24 = getelementptr inbounds %struct.arc, %struct.arc* %i16, i32 0, i32 2
  %i17 = load %struct.node*, %struct.node** %head24, align 8
  %arc_tmp = getelementptr inbounds %struct.node, %struct.node* %i17, i32 0, i32 9
  store %struct.arc* %first_of_sparse_list.0, %struct.arc** %arc_tmp, align 8
  %add.ptr25 = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i64 1
  br label %if.end26

if.end26:                                         ; preds = %if.then22, %for.body18
  %first_of_sparse_list.1 = phi %struct.arc* [ %add.ptr25, %if.then22 ], [ %first_of_sparse_list.0, %for.body18 ]
  %ident27 = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i32 0, i32 3
  %i18 = load i32, i32* %ident27, align 8
  %cmp28 = icmp eq i32 %i18, -1
  br i1 %cmp28, label %if.then29, label %if.end30

if.then29:                                        ; preds = %if.end26
  br label %for.inc66

if.end30:                                         ; preds = %if.end26
  %head31 = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i32 0, i32 2
  %i19 = load %struct.node*, %struct.node** %head31, align 8
  %time = getelementptr inbounds %struct.node, %struct.node* %i19, i32 0, i32 13
  %i20 = load i32, i32* %time, align 4
  %conv = sext i32 %i20 to i64
  %org_cost = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i32 0, i32 7
  %i21 = load i64, i64* %org_cost, align 8
  %sub32 = sub nsw i64 %conv, %i21
  %add33 = add nsw i64 %sub32, %sub
  %potential = getelementptr inbounds %struct.node, %struct.node* %i19, i32 0, i32 0
  %i22 = load i64, i64* %potential, align 8
  %tail34 = getelementptr inbounds %struct.arc, %struct.arc* %first_of_sparse_list.1, i32 0, i32 1
  %i23 = load %struct.node*, %struct.node** %tail34, align 8
  %arc_tmp35 = getelementptr inbounds %struct.node, %struct.node* %i23, i32 0, i32 9
  %i24 = load %struct.arc*, %struct.arc** %arc_tmp35, align 8
  br label %while.cond

while.cond:                                       ; preds = %if.end64, %if.then44, %if.end30
  %arcin.0 = phi %struct.arc* [ %i24, %if.end30 ], [ %i28, %if.then44 ], [ %i33, %if.end64 ]
  %new_arcs.1 = phi i64 [ %new_arcs.0, %if.end30 ], [ %new_arcs.1, %if.then44 ], [ %new_arcs.3, %if.end64 ]
  %tobool36 = icmp ne %struct.arc* %arcin.0, null
  br i1 %tobool36, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %tail37 = getelementptr inbounds %struct.arc, %struct.arc* %arcin.0, i32 0, i32 1
  %i25 = load %struct.node*, %struct.node** %tail37, align 8
  %time38 = getelementptr inbounds %struct.node, %struct.node* %i25, i32 0, i32 13
  %i26 = load i32, i32* %time38, align 4
  %conv39 = sext i32 %i26 to i64
  %org_cost40 = getelementptr inbounds %struct.arc, %struct.arc* %arcin.0, i32 0, i32 7
  %i27 = load i64, i64* %org_cost40, align 8
  %add41 = add nsw i64 %conv39, %i27
  %cmp42 = icmp sgt i64 %add41, %add33
  br i1 %cmp42, label %if.then44, label %if.end46

if.then44:                                        ; preds = %while.body
  %arc_tmp45 = getelementptr inbounds %struct.node, %struct.node* %i25, i32 0, i32 9
  %i28 = load %struct.arc*, %struct.arc** %arc_tmp45, align 8
  br label %while.cond

if.end46:                                         ; preds = %while.body
  %potential47 = getelementptr inbounds %struct.node, %struct.node* %i25, i32 0, i32 0
  %i29 = load i64, i64* %potential47, align 8
  %sub48 = sub nsw i64 30, %i29
  %potential49 = getelementptr inbounds %struct.node, %struct.node* %i19, i32 0, i32 0
  %i30 = load i64, i64* %potential49, align 8
  %add50 = add nsw i64 %sub48, %i30
  %cmp51 = icmp slt i64 %add50, 0
  br i1 %cmp51, label %if.then53, label %if.end64

if.then53:                                        ; preds = %if.end46
  %max_residual_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  %i31 = load i64, i64* %max_residual_new_m, align 8
  %cmp54 = icmp slt i64 %new_arcs.1, %i31
  br i1 %cmp54, label %if.then56, label %if.else

if.then56:                                        ; preds = %if.then53
  call void @insert_new_arc(%struct.arc* %i9, i64 %new_arcs.1, %struct.node* %i25, %struct.node* %i19, i64 30, i64 %add50)
  %inc57 = add nsw i64 %new_arcs.1, 1
  br label %if.end63

if.else:                                          ; preds = %if.then53
  %arrayidx58 = getelementptr inbounds %struct.arc, %struct.arc* %i9, i64 0
  %flow = getelementptr inbounds %struct.arc, %struct.arc* %arrayidx58, i32 0, i32 6
  %i32 = load i64, i64* %flow, align 8
  %cmp59 = icmp sgt i64 %i32, %add50
  br i1 %cmp59, label %if.then61, label %if.end62

if.then61:                                        ; preds = %if.else
  call void @replace_weaker_arc(%struct.network* %net, %struct.arc* %i9, %struct.node* %i25, %struct.node* %i19, i64 30, i64 %add50)
  br label %if.end62

if.end62:                                         ; preds = %if.then61, %if.else
  br label %if.end63

if.end63:                                         ; preds = %if.end62, %if.then56
  %new_arcs.2 = phi i64 [ %inc57, %if.then56 ], [ %new_arcs.1, %if.end62 ]
  br label %if.end64

if.end64:                                         ; preds = %if.end63, %if.end46
  %new_arcs.3 = phi i64 [ %new_arcs.2, %if.end63 ], [ %new_arcs.1, %if.end46 ]
  %arc_tmp65 = getelementptr inbounds %struct.node, %struct.node* %i25, i32 0, i32 9
  %i33 = load %struct.arc*, %struct.arc** %arc_tmp65, align 8
  br label %while.cond

while.end:                                        ; preds = %while.cond
  br label %for.inc66

for.inc66:                                        ; preds = %while.end, %if.then29
  %new_arcs.4 = phi i64 [ %new_arcs.0, %if.then29 ], [ %new_arcs.1, %while.end ]
  %inc67 = add nsw i64 %i.1, 1
  %add.ptr68 = getelementptr inbounds %struct.arc, %struct.arc* %arcout.1, i64 3
  br label %for.cond16

for.end69:                                        ; preds = %for.cond16
  %tobool70 = icmp ne i64 %new_arcs.0, 0
  br i1 %tobool70, label %if.then71, label %if.end109

if.then71:                                        ; preds = %for.end69
  %stop_arcs72 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i34 = load %struct.arc*, %struct.arc** %stop_arcs72, align 8
  %stop_arcs73 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i35 = load %struct.arc*, %struct.arc** %stop_arcs73, align 8
  %add.ptr74 = getelementptr inbounds %struct.arc, %struct.arc* %i35, i64 %new_arcs.0
  store %struct.arc* %add.ptr74, %struct.arc** %stop_arcs73, align 8
  %stop_arcs75 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i36 = load %struct.arc*, %struct.arc** %stop_arcs75, align 8
  %i37 = bitcast %struct.arc* %i36 to i8*
  %i38 = bitcast i8* %i37 to %struct.arc*
  %tobool76 = icmp ne i64 %resized.1, 0
  br i1 %tobool76, label %if.then77, label %if.else86

if.then77:                                        ; preds = %if.then71
  br label %for.cond78

for.cond78:                                       ; preds = %for.inc84, %if.then77
  %arcnew.0 = phi %struct.arc* [ %i34, %if.then77 ], [ %incdec.ptr, %for.inc84 ]
  %cmp79 = icmp ne %struct.arc* %arcnew.0, %i38
  br i1 %cmp79, label %for.body81, label %for.end85

for.body81:                                       ; preds = %for.cond78
  %flow82 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.0, i32 0, i32 6
  store i64 0, i64* %flow82, align 8
  %ident83 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.0, i32 0, i32 3
  store i32 1, i32* %ident83, align 8
  br label %for.inc84

for.inc84:                                        ; preds = %for.body81
  %incdec.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.0, i32 1
  br label %for.cond78

for.end85:                                        ; preds = %for.cond78
  br label %if.end103

if.else86:                                        ; preds = %if.then71
  br label %for.cond87

for.cond87:                                       ; preds = %for.inc100, %if.else86
  %arcnew.1 = phi %struct.arc* [ %i34, %if.else86 ], [ %incdec.ptr101, %for.inc100 ]
  %cmp88 = icmp ne %struct.arc* %arcnew.1, %i38
  br i1 %cmp88, label %for.body90, label %for.end102

for.body90:                                       ; preds = %for.cond87
  %flow91 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 6
  store i64 0, i64* %flow91, align 8
  %ident92 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 3
  store i32 1, i32* %ident92, align 8
  %tail93 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 1
  %i39 = load %struct.node*, %struct.node** %tail93, align 8
  %firstout94 = getelementptr inbounds %struct.node, %struct.node* %i39, i32 0, i32 7
  %i40 = load %struct.arc*, %struct.arc** %firstout94, align 8
  %nextout = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 4
  store %struct.arc* %i40, %struct.arc** %nextout, align 8
  %tail95 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 1
  %i41 = load %struct.node*, %struct.node** %tail95, align 8
  %firstout96 = getelementptr inbounds %struct.node, %struct.node* %i41, i32 0, i32 7
  store %struct.arc* %arcnew.1, %struct.arc** %firstout96, align 8
  %head97 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 2
  %i42 = load %struct.node*, %struct.node** %head97, align 8
  %firstin = getelementptr inbounds %struct.node, %struct.node* %i42, i32 0, i32 8
  %i43 = load %struct.arc*, %struct.arc** %firstin, align 8
  %nextin = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 5
  store %struct.arc* %i43, %struct.arc** %nextin, align 8
  %head98 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 0, i32 2
  %i44 = load %struct.node*, %struct.node** %head98, align 8
  %firstin99 = getelementptr inbounds %struct.node, %struct.node* %i44, i32 0, i32 8
  store %struct.arc* %arcnew.1, %struct.arc** %firstin99, align 8
  br label %for.inc100

for.inc100:                                       ; preds = %for.body90
  %incdec.ptr101 = getelementptr inbounds %struct.arc, %struct.arc* %arcnew.1, i32 1
  br label %for.cond87

for.end102:                                       ; preds = %for.cond87
  br label %if.end103

if.end103:                                        ; preds = %for.end102, %for.end85
  %m104 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i45 = load i64, i64* %m104, align 8
  %add105 = add nsw i64 %i45, %new_arcs.0
  store i64 %add105, i64* %m104, align 8
  %m_impl = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 7
  %i46 = load i64, i64* %m_impl, align 8
  %add106 = add nsw i64 %i46, %new_arcs.0
  store i64 %add106, i64* %m_impl, align 8
  %max_residual_new_m107 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  %i47 = load i64, i64* %max_residual_new_m107, align 8
  %sub108 = sub nsw i64 %i47, %new_arcs.0
  store i64 %sub108, i64* %max_residual_new_m107, align 8
  br label %if.end109

if.end109:                                        ; preds = %if.end103, %for.end69
  br label %return

return:                                           ; preds = %if.end109, %if.then10
  %retval.0 = phi i64 [ -1, %if.then10 ], [ %new_arcs.0, %if.end109 ]
  ret i64 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @suspend_impl(%struct.network* %net, i64 %threshold, i64 %all) #0 {
entry:
  %tobool = icmp ne i64 %all, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %m_impl = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 7
  %i = load i64, i64* %m_impl, align 8
  br label %if.end25

if.else:                                          ; preds = %entry
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i1 = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %i2 = bitcast %struct.arc* %i1 to i8*
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i3 = load %struct.arc*, %struct.arc** %arcs, align 8
  %m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i4 = load i64, i64* %m, align 8
  %m_impl1 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 7
  %i5 = load i64, i64* %m_impl1, align 8
  %sub = sub nsw i64 %i4, %i5
  %arrayidx = getelementptr inbounds %struct.arc, %struct.arc* %i3, i64 %sub
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.else
  %susp.0 = phi i64 [ 0, %if.else ], [ %susp.1, %for.inc ]
  %new_arc.0 = phi %struct.arc* [ %arrayidx, %if.else ], [ %new_arc.1, %for.inc ]
  %arc.0 = phi %struct.arc* [ %arrayidx, %if.else ], [ %incdec.ptr24, %for.inc ]
  %i6 = bitcast i8* %i2 to %struct.arc*
  %cmp = icmp ult %struct.arc* %arc.0, %i6
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i7 = load i32, i32* %ident, align 8
  %cmp2 = icmp eq i32 %i7, 1
  br i1 %cmp2, label %if.then3, label %if.else6

if.then3:                                         ; preds = %for.body
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 0
  %i8 = load i64, i64* %cost, align 8
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i9 = load %struct.node*, %struct.node** %tail, align 8
  %potential = getelementptr inbounds %struct.node, %struct.node* %i9, i32 0, i32 0
  %i10 = load i64, i64* %potential, align 8
  %sub4 = sub nsw i64 %i8, %i10
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i11 = load %struct.node*, %struct.node** %head, align 8
  %potential5 = getelementptr inbounds %struct.node, %struct.node* %i11, i32 0, i32 0
  %i12 = load i64, i64* %potential5, align 8
  %add = add nsw i64 %sub4, %i12
  br label %if.end19

if.else6:                                         ; preds = %for.body
  %ident7 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i13 = load i32, i32* %ident7, align 8
  %cmp8 = icmp eq i32 %i13, 0
  br i1 %cmp8, label %if.then9, label %if.end18

if.then9:                                         ; preds = %if.else6
  %tail10 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i14 = load %struct.node*, %struct.node** %tail10, align 8
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %i14, i32 0, i32 6
  %i15 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %cmp11 = icmp eq %struct.arc* %i15, %arc.0
  br i1 %cmp11, label %if.then12, label %if.else15

if.then12:                                        ; preds = %if.then9
  %tail13 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i16 = load %struct.node*, %struct.node** %tail13, align 8
  %basic_arc14 = getelementptr inbounds %struct.node, %struct.node* %i16, i32 0, i32 6
  store %struct.arc* %new_arc.0, %struct.arc** %basic_arc14, align 8
  br label %if.end

if.else15:                                        ; preds = %if.then9
  %head16 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i17 = load %struct.node*, %struct.node** %head16, align 8
  %basic_arc17 = getelementptr inbounds %struct.node, %struct.node* %i17, i32 0, i32 6
  store %struct.arc* %new_arc.0, %struct.arc** %basic_arc17, align 8
  br label %if.end

if.end:                                           ; preds = %if.else15, %if.then12
  br label %if.end18

if.end18:                                         ; preds = %if.end, %if.else6
  br label %if.end19

if.end19:                                         ; preds = %if.end18, %if.then3
  %red_cost.0 = phi i64 [ %add, %if.then3 ], [ -2, %if.end18 ]
  %cmp20 = icmp sgt i64 %red_cost.0, %threshold
  br i1 %cmp20, label %if.then21, label %if.else22

if.then21:                                        ; preds = %if.end19
  %inc = add nsw i64 %susp.0, 1
  br label %if.end23

if.else22:                                        ; preds = %if.end19
  %i18 = bitcast %struct.arc* %new_arc.0 to i8*
  %i19 = bitcast %struct.arc* %arc.0 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %i18, i8* align 8 %i19, i64 64, i1 false)
  %incdec.ptr = getelementptr inbounds %struct.arc, %struct.arc* %new_arc.0, i32 1
  br label %if.end23

if.end23:                                         ; preds = %if.else22, %if.then21
  %susp.1 = phi i64 [ %inc, %if.then21 ], [ %susp.0, %if.else22 ]
  %new_arc.1 = phi %struct.arc* [ %new_arc.0, %if.then21 ], [ %incdec.ptr, %if.else22 ]
  br label %for.inc

for.inc:                                          ; preds = %if.end23
  %incdec.ptr24 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %if.end25

if.end25:                                         ; preds = %for.end, %if.then
  %susp.2 = phi i64 [ %i, %if.then ], [ %susp.0, %for.end ]
  %tobool26 = icmp ne i64 %susp.2, 0
  br i1 %tobool26, label %if.then27, label %if.end34

if.then27:                                        ; preds = %if.end25
  %m28 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i20 = load i64, i64* %m28, align 8
  %sub29 = sub nsw i64 %i20, %susp.2
  store i64 %sub29, i64* %m28, align 8
  %m_impl30 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 7
  %i21 = load i64, i64* %m_impl30, align 8
  %sub31 = sub nsw i64 %i21, %susp.2
  store i64 %sub31, i64* %m_impl30, align 8
  %stop_arcs32 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i22 = load %struct.arc*, %struct.arc** %stop_arcs32, align 8
  %idx.neg = sub i64 0, %susp.2
  %add.ptr = getelementptr inbounds %struct.arc, %struct.arc* %i22, i64 %idx.neg
  store %struct.arc* %add.ptr, %struct.arc** %stop_arcs32, align 8
  %max_residual_new_m = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 8
  %i23 = load i64, i64* %max_residual_new_m, align 8
  %add33 = add nsw i64 %i23, %susp.2
  store i64 %add33, i64* %max_residual_new_m, align 8
  call void @refresh_neighbour_lists(%struct.network* %net)
  br label %if.end34

if.end34:                                         ; preds = %if.then27, %if.end25
  ret i64 %susp.2
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #5

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @primal_start_artificial(%struct.network* %net) #0 {
entry:
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i = load %struct.node*, %struct.node** %nodes, align 8
  %incdec.ptr = getelementptr inbounds %struct.node, %struct.node* %i, i32 1
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 6
  store %struct.arc* null, %struct.arc** %basic_arc, align 8
  %pred = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 3
  store %struct.node* null, %struct.node** %pred, align 8
  %child = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 2
  store %struct.node* %incdec.ptr, %struct.node** %child, align 8
  %sibling = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 4
  store %struct.node* null, %struct.node** %sibling, align 8
  %sibling_prev = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 5
  store %struct.node* null, %struct.node** %sibling_prev, align 8
  %n = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i1 = load i64, i64* %n, align 8
  %add = add nsw i64 %i1, 1
  %depth = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 11
  store i64 %add, i64* %depth, align 8
  %orientation = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 1
  store i32 0, i32* %orientation, align 8
  %potential = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 0
  store i64 -100000000, i64* %potential, align 8
  %flow = getelementptr inbounds %struct.node, %struct.node* %i, i32 0, i32 10
  store i64 0, i64* %flow, align 8
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i2 = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %i3 = bitcast %struct.arc* %i2 to i8*
  %arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i4 = load %struct.arc*, %struct.arc** %arcs, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %arc.0 = phi %struct.arc* [ %i4, %entry ], [ %incdec.ptr3, %for.inc ]
  %i5 = bitcast i8* %i3 to %struct.arc*
  %cmp = icmp ne %struct.arc* %arc.0, %i5
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i6 = load i32, i32* %ident, align 8
  %cmp1 = icmp ne i32 %i6, -1
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  %ident2 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  store i32 1, i32* %ident2, align 8
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %incdec.ptr3 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %dummy_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 25
  %i7 = load %struct.arc*, %struct.arc** %dummy_arcs, align 8
  %stop_nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 22
  %i8 = load %struct.node*, %struct.node** %stop_nodes, align 8
  %i9 = bitcast %struct.node* %i8 to i8*
  br label %for.cond4

for.cond4:                                        ; preds = %for.inc18, %for.end
  %arc.1 = phi %struct.arc* [ %i7, %for.end ], [ %incdec.ptr19, %for.inc18 ]
  %node.0 = phi %struct.node* [ %incdec.ptr, %for.end ], [ %incdec.ptr20, %for.inc18 ]
  %i10 = bitcast i8* %i9 to %struct.node*
  %cmp5 = icmp ne %struct.node* %node.0, %i10
  br i1 %cmp5, label %for.body6, label %for.end21

for.body6:                                        ; preds = %for.cond4
  %basic_arc7 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 6
  store %struct.arc* %arc.1, %struct.arc** %basic_arc7, align 8
  %pred8 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 3
  store %struct.node* %i, %struct.node** %pred8, align 8
  %child9 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 2
  store %struct.node* null, %struct.node** %child9, align 8
  %add.ptr = getelementptr inbounds %struct.node, %struct.node* %node.0, i64 1
  %sibling10 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 4
  store %struct.node* %add.ptr, %struct.node** %sibling10, align 8
  %add.ptr11 = getelementptr inbounds %struct.node, %struct.node* %node.0, i64 -1
  %sibling_prev12 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 5
  store %struct.node* %add.ptr11, %struct.node** %sibling_prev12, align 8
  %depth13 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 11
  store i64 1, i64* %depth13, align 8
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 0
  store i64 100000000, i64* %cost, align 8
  %ident14 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 3
  store i32 0, i32* %ident14, align 8
  %orientation15 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 1
  store i32 1, i32* %orientation15, align 8
  %potential16 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 0
  store i64 0, i64* %potential16, align 8
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 1
  store %struct.node* %node.0, %struct.node** %tail, align 8
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 0, i32 2
  store %struct.node* %i, %struct.node** %head, align 8
  %flow17 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 0, i32 10
  store i64 0, i64* %flow17, align 8
  br label %for.inc18

for.inc18:                                        ; preds = %for.body6
  %incdec.ptr19 = getelementptr inbounds %struct.arc, %struct.arc* %arc.1, i32 1
  %incdec.ptr20 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 1
  br label %for.cond4

for.end21:                                        ; preds = %for.cond4
  %incdec.ptr22 = getelementptr inbounds %struct.node, %struct.node* %node.0, i32 -1
  %incdec.ptr23 = getelementptr inbounds %struct.node, %struct.node* %i, i32 1
  %sibling24 = getelementptr inbounds %struct.node, %struct.node* %incdec.ptr22, i32 0, i32 4
  store %struct.node* null, %struct.node** %sibling24, align 8
  %sibling_prev25 = getelementptr inbounds %struct.node, %struct.node* %incdec.ptr23, i32 0, i32 5
  store %struct.node* null, %struct.node** %sibling_prev25, align 8
  ret i64 0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @write_circulations(i8* %outfile, %struct.network* %net) #0 {
entry:
  %stop_arcs = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i = load %struct.arc*, %struct.arc** %stop_arcs, align 8
  %m_impl = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 7
  %i1 = load i64, i64* %m_impl, align 8
  %idx.neg = sub i64 0, %i1
  %add.ptr = getelementptr inbounds %struct.arc, %struct.arc* %i, i64 %idx.neg
  %call = call noalias %struct._IO_FILE* @fopen(i8* %outfile, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.38, i64 0, i64 0))
  %cmp = icmp eq %struct._IO_FILE* %call, null
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  call void @refresh_neighbour_lists(%struct.network* %net)
  %nodes = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 21
  %i2 = load %struct.node*, %struct.node** %nodes, align 8
  %n = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 2
  %i3 = load i64, i64* %n, align 8
  %arrayidx = getelementptr inbounds %struct.node, %struct.node* %i2, i64 %i3
  %firstout = getelementptr inbounds %struct.node, %struct.node* %arrayidx, i32 0, i32 7
  %i4 = load %struct.arc*, %struct.arc** %firstout, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.inc30, %if.end
  %block.0 = phi %struct.arc* [ %i4, %if.end ], [ %i15, %for.inc30 ]
  %tobool = icmp ne %struct.arc* %block.0, null
  br i1 %tobool, label %for.body, label %for.end32

for.body:                                         ; preds = %for.cond
  %flow = getelementptr inbounds %struct.arc, %struct.arc* %block.0, i32 0, i32 6
  %i5 = load i64, i64* %flow, align 8
  %tobool1 = icmp ne i64 %i5, 0
  br i1 %tobool1, label %if.then2, label %if.end29

if.then2:                                         ; preds = %for.body
  %call3 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %call, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1.39, i64 0, i64 0))
  br label %while.cond

while.cond:                                       ; preds = %if.end28, %if.then2
  %arc.0 = phi %struct.arc* [ %block.0, %if.then2 ], [ %arc.1, %if.end28 ]
  %tobool4 = icmp ne %struct.arc* %arc.0, null
  br i1 %tobool4, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %cmp5 = icmp uge %struct.arc* %arc.0, %add.ptr
  br i1 %cmp5, label %if.then6, label %if.end8

if.then6:                                         ; preds = %while.body
  %call7 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %call, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2.40, i64 0, i64 0))
  br label %if.end8

if.end8:                                          ; preds = %if.then6, %while.body
  %head = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i6 = load %struct.node*, %struct.node** %head, align 8
  %number = getelementptr inbounds %struct.node, %struct.node* %i6, i32 0, i32 12
  %i7 = load i32, i32* %number, align 8
  %sub = sub nsw i32 0, %i7
  %call9 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %call, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.3.41, i64 0, i64 0), i32 %sub)
  %head10 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i8 = load %struct.node*, %struct.node** %head10, align 8
  %n_trips = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 3
  %i9 = load i64, i64* %n_trips, align 8
  %arrayidx11 = getelementptr inbounds %struct.node, %struct.node* %i8, i64 %i9
  %firstout12 = getelementptr inbounds %struct.node, %struct.node* %arrayidx11, i32 0, i32 7
  %i10 = load %struct.arc*, %struct.arc** %firstout12, align 8
  br label %for.cond13

for.cond13:                                       ; preds = %for.inc, %if.end8
  %arc2.0 = phi %struct.arc* [ %i10, %if.end8 ], [ %i12, %for.inc ]
  %tobool14 = icmp ne %struct.arc* %arc2.0, null
  br i1 %tobool14, label %for.body15, label %for.end

for.body15:                                       ; preds = %for.cond13
  %flow16 = getelementptr inbounds %struct.arc, %struct.arc* %arc2.0, i32 0, i32 6
  %i11 = load i64, i64* %flow16, align 8
  %tobool17 = icmp ne i64 %i11, 0
  br i1 %tobool17, label %if.then18, label %if.end19

if.then18:                                        ; preds = %for.body15
  br label %for.end

if.end19:                                         ; preds = %for.body15
  br label %for.inc

for.inc:                                          ; preds = %if.end19
  %nextout = getelementptr inbounds %struct.arc, %struct.arc* %arc2.0, i32 0, i32 4
  %i12 = load %struct.arc*, %struct.arc** %nextout, align 8
  br label %for.cond13

for.end:                                          ; preds = %if.then18, %for.cond13
  %tobool20 = icmp ne %struct.arc* %arc2.0, null
  br i1 %tobool20, label %if.end23, label %if.then21

if.then21:                                        ; preds = %for.end
  %call22 = call i32 @fclose(%struct._IO_FILE* %call)
  br label %return

if.end23:                                         ; preds = %for.end
  %head24 = getelementptr inbounds %struct.arc, %struct.arc* %arc2.0, i32 0, i32 2
  %i13 = load %struct.node*, %struct.node** %head24, align 8
  %number25 = getelementptr inbounds %struct.node, %struct.node* %i13, i32 0, i32 12
  %i14 = load i32, i32* %number25, align 8
  %tobool26 = icmp ne i32 %i14, 0
  br i1 %tobool26, label %if.then27, label %if.else

if.then27:                                        ; preds = %if.end23
  br label %if.end28

if.else:                                          ; preds = %if.end23
  br label %if.end28

if.end28:                                         ; preds = %if.else, %if.then27
  %arc.1 = phi %struct.arc* [ %arc2.0, %if.then27 ], [ null, %if.else ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  br label %if.end29

if.end29:                                         ; preds = %while.end, %for.body
  br label %for.inc30

for.inc30:                                        ; preds = %if.end29
  %nextout31 = getelementptr inbounds %struct.arc, %struct.arc* %block.0, i32 0, i32 4
  %i15 = load %struct.arc*, %struct.arc** %nextout31, align 8
  br label %for.cond

for.end32:                                        ; preds = %for.cond
  %call33 = call i32 @fclose(%struct._IO_FILE* %call)
  br label %return

return:                                           ; preds = %for.end32, %if.then21, %if.then
  %retval.0 = phi i64 [ -1, %if.then ], [ -1, %if.then21 ], [ 0, %for.end32 ]
  ret i64 %retval.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @update_tree(i64 %cycle_ori, i64 %new_orientation, i64 %delta, i64 %new_flow, %struct.node* %iplus, %struct.node* %jplus, %struct.node* %iminus, %struct.node* %jminus, %struct.node* %w, %struct.arc* %bea, i64 %sigma, i64 %feas_tol) #0 {
entry:
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %bea, i32 0, i32 1
  %i = load %struct.node*, %struct.node** %tail, align 8
  %cmp = icmp eq %struct.node* %i, %jplus
  br i1 %cmp, label %land.lhs.true, label %lor.lhs.false

land.lhs.true:                                    ; preds = %entry
  %cmp1 = icmp slt i64 %sigma, 0
  br i1 %cmp1, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %land.lhs.true, %entry
  %tail2 = getelementptr inbounds %struct.arc, %struct.arc* %bea, i32 0, i32 1
  %i1 = load %struct.node*, %struct.node** %tail2, align 8
  %cmp3 = icmp eq %struct.node* %i1, %iplus
  br i1 %cmp3, label %land.lhs.true4, label %if.else

land.lhs.true4:                                   ; preds = %lor.lhs.false
  %cmp5 = icmp sgt i64 %sigma, 0
  br i1 %cmp5, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true4, %land.lhs.true
  %cmp6 = icmp sge i64 %sigma, 0
  br i1 %cmp6, label %cond.true, label %cond.false

cond.true:                                        ; preds = %if.then
  br label %cond.end

cond.false:                                       ; preds = %if.then
  %sub = sub nsw i64 0, %sigma
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i64 [ %sigma, %cond.true ], [ %sub, %cond.false ]
  br label %if.end

if.else:                                          ; preds = %land.lhs.true4, %lor.lhs.false
  %cmp7 = icmp sge i64 %sigma, 0
  br i1 %cmp7, label %cond.true8, label %cond.false9

cond.true8:                                       ; preds = %if.else
  br label %cond.end11

cond.false9:                                      ; preds = %if.else
  %sub10 = sub nsw i64 0, %sigma
  br label %cond.end11

cond.end11:                                       ; preds = %cond.false9, %cond.true8
  %cond12 = phi i64 [ %sigma, %cond.true8 ], [ %sub10, %cond.false9 ]
  %sub13 = sub nsw i64 0, %cond12
  br label %if.end

if.end:                                           ; preds = %cond.end11, %cond.end
  %sigma.addr.0 = phi i64 [ %cond, %cond.end ], [ %sub13, %cond.end11 ]
  %potential = getelementptr inbounds %struct.node, %struct.node* %iminus, i32 0, i32 0
  %i2 = load i64, i64* %potential, align 8
  %add = add nsw i64 %i2, %sigma.addr.0
  store i64 %add, i64* %potential, align 8
  br label %RECURSION

RECURSION:                                        ; preds = %ITERATION, %if.end
  %father.0 = phi %struct.node* [ %iminus, %if.end ], [ %temp.0, %ITERATION ]
  %child = getelementptr inbounds %struct.node, %struct.node* %father.0, i32 0, i32 2
  %i3 = load %struct.node*, %struct.node** %child, align 8
  %tobool = icmp ne %struct.node* %i3, null
  br i1 %tobool, label %if.then14, label %if.end17

if.then14:                                        ; preds = %RECURSION
  br label %ITERATION

ITERATION:                                        ; preds = %if.then22, %if.then14
  %temp.0 = phi %struct.node* [ %i3, %if.then14 ], [ %i5, %if.then22 ]
  %potential15 = getelementptr inbounds %struct.node, %struct.node* %temp.0, i32 0, i32 0
  %i4 = load i64, i64* %potential15, align 8
  %add16 = add nsw i64 %i4, %sigma.addr.0
  store i64 %add16, i64* %potential15, align 8
  br label %RECURSION

if.end17:                                         ; preds = %RECURSION
  br label %TEST

TEST:                                             ; preds = %if.end23, %if.end17
  %father.1 = phi %struct.node* [ %father.0, %if.end17 ], [ %i6, %if.end23 ]
  %cmp18 = icmp eq %struct.node* %father.1, %iminus
  br i1 %cmp18, label %if.then19, label %if.end20

if.then19:                                        ; preds = %TEST
  br label %CONTINUE

if.end20:                                         ; preds = %TEST
  %sibling = getelementptr inbounds %struct.node, %struct.node* %father.1, i32 0, i32 4
  %i5 = load %struct.node*, %struct.node** %sibling, align 8
  %tobool21 = icmp ne %struct.node* %i5, null
  br i1 %tobool21, label %if.then22, label %if.end23

if.then22:                                        ; preds = %if.end20
  br label %ITERATION

if.end23:                                         ; preds = %if.end20
  %pred = getelementptr inbounds %struct.node, %struct.node* %father.1, i32 0, i32 3
  %i6 = load %struct.node*, %struct.node** %pred, align 8
  br label %TEST

CONTINUE:                                         ; preds = %if.then19
  %pred24 = getelementptr inbounds %struct.node, %struct.node* %iplus, i32 0, i32 3
  %i7 = load %struct.node*, %struct.node** %pred24, align 8
  %depth = getelementptr inbounds %struct.node, %struct.node* %iminus, i32 0, i32 11
  %i8 = load i64, i64* %depth, align 8
  br label %while.cond

while.cond:                                       ; preds = %if.end61, %CONTINUE
  %new_basic_arc.0 = phi %struct.arc* [ %bea, %CONTINUE ], [ %i22, %if.end61 ]
  %father.2 = phi %struct.node* [ %i7, %CONTINUE ], [ %i24, %if.end61 ]
  %temp.1 = phi %struct.node* [ %iplus, %CONTINUE ], [ %father.2, %if.end61 ]
  %new_pred.0 = phi %struct.node* [ %jplus, %CONTINUE ], [ %temp.1, %if.end61 ]
  %new_flow.addr.0 = phi i64 [ %new_flow, %CONTINUE ], [ %flow_temp.0, %if.end61 ]
  %new_depth.0 = phi i64 [ %i8, %CONTINUE ], [ %sub68, %if.end61 ]
  %new_orientation.addr.0 = phi i64 [ %new_orientation, %CONTINUE ], [ %conv, %if.end61 ]
  %cmp25 = icmp ne %struct.node* %temp.1, %jminus
  br i1 %cmp25, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %sibling26 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  %i9 = load %struct.node*, %struct.node** %sibling26, align 8
  %tobool27 = icmp ne %struct.node* %i9, null
  br i1 %tobool27, label %if.then28, label %if.end31

if.then28:                                        ; preds = %while.body
  %sibling_prev = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 5
  %i10 = load %struct.node*, %struct.node** %sibling_prev, align 8
  %sibling29 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  %i11 = load %struct.node*, %struct.node** %sibling29, align 8
  %sibling_prev30 = getelementptr inbounds %struct.node, %struct.node* %i11, i32 0, i32 5
  store %struct.node* %i10, %struct.node** %sibling_prev30, align 8
  br label %if.end31

if.end31:                                         ; preds = %if.then28, %while.body
  %sibling_prev32 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 5
  %i12 = load %struct.node*, %struct.node** %sibling_prev32, align 8
  %tobool33 = icmp ne %struct.node* %i12, null
  br i1 %tobool33, label %if.then34, label %if.else38

if.then34:                                        ; preds = %if.end31
  %sibling35 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  %i13 = load %struct.node*, %struct.node** %sibling35, align 8
  %sibling_prev36 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 5
  %i14 = load %struct.node*, %struct.node** %sibling_prev36, align 8
  %sibling37 = getelementptr inbounds %struct.node, %struct.node* %i14, i32 0, i32 4
  store %struct.node* %i13, %struct.node** %sibling37, align 8
  br label %if.end41

if.else38:                                        ; preds = %if.end31
  %sibling39 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  %i15 = load %struct.node*, %struct.node** %sibling39, align 8
  %child40 = getelementptr inbounds %struct.node, %struct.node* %father.2, i32 0, i32 2
  store %struct.node* %i15, %struct.node** %child40, align 8
  br label %if.end41

if.end41:                                         ; preds = %if.else38, %if.then34
  %pred42 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 3
  store %struct.node* %new_pred.0, %struct.node** %pred42, align 8
  %child43 = getelementptr inbounds %struct.node, %struct.node* %new_pred.0, i32 0, i32 2
  %i16 = load %struct.node*, %struct.node** %child43, align 8
  %sibling44 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  store %struct.node* %i16, %struct.node** %sibling44, align 8
  %sibling45 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  %i17 = load %struct.node*, %struct.node** %sibling45, align 8
  %tobool46 = icmp ne %struct.node* %i17, null
  br i1 %tobool46, label %if.then47, label %if.end50

if.then47:                                        ; preds = %if.end41
  %sibling48 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 4
  %i18 = load %struct.node*, %struct.node** %sibling48, align 8
  %sibling_prev49 = getelementptr inbounds %struct.node, %struct.node* %i18, i32 0, i32 5
  store %struct.node* %temp.1, %struct.node** %sibling_prev49, align 8
  br label %if.end50

if.end50:                                         ; preds = %if.then47, %if.end41
  %child51 = getelementptr inbounds %struct.node, %struct.node* %new_pred.0, i32 0, i32 2
  store %struct.node* %temp.1, %struct.node** %child51, align 8
  %sibling_prev52 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 5
  store %struct.node* null, %struct.node** %sibling_prev52, align 8
  %orientation = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 1
  %i19 = load i32, i32* %orientation, align 8
  %tobool53 = icmp ne i32 %i19, 0
  %lnot = xor i1 %tobool53, true
  %lnot.ext = zext i1 %lnot to i32
  %conv = sext i32 %lnot.ext to i64
  %cmp54 = icmp eq i64 %conv, %cycle_ori
  br i1 %cmp54, label %if.then56, label %if.else58

if.then56:                                        ; preds = %if.end50
  %flow = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 10
  %i20 = load i64, i64* %flow, align 8
  %add57 = add nsw i64 %i20, %delta
  br label %if.end61

if.else58:                                        ; preds = %if.end50
  %flow59 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 10
  %i21 = load i64, i64* %flow59, align 8
  %sub60 = sub nsw i64 %i21, %delta
  br label %if.end61

if.end61:                                         ; preds = %if.else58, %if.then56
  %flow_temp.0 = phi i64 [ %add57, %if.then56 ], [ %sub60, %if.else58 ]
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 6
  %i22 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %depth62 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 11
  %i23 = load i64, i64* %depth62, align 8
  %conv63 = trunc i64 %new_orientation.addr.0 to i32
  %orientation64 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 1
  store i32 %conv63, i32* %orientation64, align 8
  %flow65 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 10
  store i64 %new_flow.addr.0, i64* %flow65, align 8
  %basic_arc66 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 6
  store %struct.arc* %new_basic_arc.0, %struct.arc** %basic_arc66, align 8
  %depth67 = getelementptr inbounds %struct.node, %struct.node* %temp.1, i32 0, i32 11
  store i64 %new_depth.0, i64* %depth67, align 8
  %sub68 = sub nsw i64 %i8, %i23
  %pred69 = getelementptr inbounds %struct.node, %struct.node* %father.2, i32 0, i32 3
  %i24 = load %struct.node*, %struct.node** %pred69, align 8
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %cmp70 = icmp sgt i64 %delta, %feas_tol
  br i1 %cmp70, label %if.then72, label %if.else109

if.then72:                                        ; preds = %while.end
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.then72
  %temp.2 = phi %struct.node* [ %jminus, %if.then72 ], [ %i29, %for.inc ]
  %cmp73 = icmp ne %struct.node* %temp.2, %w
  br i1 %cmp73, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %depth75 = getelementptr inbounds %struct.node, %struct.node* %temp.2, i32 0, i32 11
  %i25 = load i64, i64* %depth75, align 8
  %sub76 = sub nsw i64 %i25, %i8
  store i64 %sub76, i64* %depth75, align 8
  %orientation77 = getelementptr inbounds %struct.node, %struct.node* %temp.2, i32 0, i32 1
  %i26 = load i32, i32* %orientation77, align 8
  %conv78 = sext i32 %i26 to i64
  %cmp79 = icmp ne i64 %conv78, %cycle_ori
  br i1 %cmp79, label %if.then81, label %if.else84

if.then81:                                        ; preds = %for.body
  %flow82 = getelementptr inbounds %struct.node, %struct.node* %temp.2, i32 0, i32 10
  %i27 = load i64, i64* %flow82, align 8
  %add83 = add nsw i64 %i27, %delta
  store i64 %add83, i64* %flow82, align 8
  br label %if.end87

if.else84:                                        ; preds = %for.body
  %flow85 = getelementptr inbounds %struct.node, %struct.node* %temp.2, i32 0, i32 10
  %i28 = load i64, i64* %flow85, align 8
  %sub86 = sub nsw i64 %i28, %delta
  store i64 %sub86, i64* %flow85, align 8
  br label %if.end87

if.end87:                                         ; preds = %if.else84, %if.then81
  br label %for.inc

for.inc:                                          ; preds = %if.end87
  %pred88 = getelementptr inbounds %struct.node, %struct.node* %temp.2, i32 0, i32 3
  %i29 = load %struct.node*, %struct.node** %pred88, align 8
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond89

for.cond89:                                       ; preds = %for.inc106, %for.end
  %temp.3 = phi %struct.node* [ %jplus, %for.end ], [ %i34, %for.inc106 ]
  %cmp90 = icmp ne %struct.node* %temp.3, %w
  br i1 %cmp90, label %for.body92, label %for.end108

for.body92:                                       ; preds = %for.cond89
  %depth93 = getelementptr inbounds %struct.node, %struct.node* %temp.3, i32 0, i32 11
  %i30 = load i64, i64* %depth93, align 8
  %add94 = add nsw i64 %i30, %i8
  store i64 %add94, i64* %depth93, align 8
  %orientation95 = getelementptr inbounds %struct.node, %struct.node* %temp.3, i32 0, i32 1
  %i31 = load i32, i32* %orientation95, align 8
  %conv96 = sext i32 %i31 to i64
  %cmp97 = icmp eq i64 %conv96, %cycle_ori
  br i1 %cmp97, label %if.then99, label %if.else102

if.then99:                                        ; preds = %for.body92
  %flow100 = getelementptr inbounds %struct.node, %struct.node* %temp.3, i32 0, i32 10
  %i32 = load i64, i64* %flow100, align 8
  %add101 = add nsw i64 %i32, %delta
  store i64 %add101, i64* %flow100, align 8
  br label %if.end105

if.else102:                                       ; preds = %for.body92
  %flow103 = getelementptr inbounds %struct.node, %struct.node* %temp.3, i32 0, i32 10
  %i33 = load i64, i64* %flow103, align 8
  %sub104 = sub nsw i64 %i33, %delta
  store i64 %sub104, i64* %flow103, align 8
  br label %if.end105

if.end105:                                        ; preds = %if.else102, %if.then99
  br label %for.inc106

for.inc106:                                       ; preds = %if.end105
  %pred107 = getelementptr inbounds %struct.node, %struct.node* %temp.3, i32 0, i32 3
  %i34 = load %struct.node*, %struct.node** %pred107, align 8
  br label %for.cond89

for.end108:                                       ; preds = %for.cond89
  br label %if.end128

if.else109:                                       ; preds = %while.end
  br label %for.cond110

for.cond110:                                      ; preds = %for.inc116, %if.else109
  %temp.4 = phi %struct.node* [ %jminus, %if.else109 ], [ %i36, %for.inc116 ]
  %cmp111 = icmp ne %struct.node* %temp.4, %w
  br i1 %cmp111, label %for.body113, label %for.end118

for.body113:                                      ; preds = %for.cond110
  %depth114 = getelementptr inbounds %struct.node, %struct.node* %temp.4, i32 0, i32 11
  %i35 = load i64, i64* %depth114, align 8
  %sub115 = sub nsw i64 %i35, %i8
  store i64 %sub115, i64* %depth114, align 8
  br label %for.inc116

for.inc116:                                       ; preds = %for.body113
  %pred117 = getelementptr inbounds %struct.node, %struct.node* %temp.4, i32 0, i32 3
  %i36 = load %struct.node*, %struct.node** %pred117, align 8
  br label %for.cond110

for.end118:                                       ; preds = %for.cond110
  br label %for.cond119

for.cond119:                                      ; preds = %for.inc125, %for.end118
  %temp.5 = phi %struct.node* [ %jplus, %for.end118 ], [ %i38, %for.inc125 ]
  %cmp120 = icmp ne %struct.node* %temp.5, %w
  br i1 %cmp120, label %for.body122, label %for.end127

for.body122:                                      ; preds = %for.cond119
  %depth123 = getelementptr inbounds %struct.node, %struct.node* %temp.5, i32 0, i32 11
  %i37 = load i64, i64* %depth123, align 8
  %add124 = add nsw i64 %i37, %i8
  store i64 %add124, i64* %depth123, align 8
  br label %for.inc125

for.inc125:                                       ; preds = %for.body122
  %pred126 = getelementptr inbounds %struct.node, %struct.node* %temp.5, i32 0, i32 3
  %i38 = load %struct.node*, %struct.node** %pred126, align 8
  br label %for.cond119

for.end127:                                       ; preds = %for.cond119
  br label %if.end128

if.end128:                                        ; preds = %for.end127, %for.end108
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local %struct.node* @primal_iminus(i64* %delta, i64* %xchange, %struct.node* %iplus, %struct.node* %jplus, %struct.node** %w) #0 {
entry:
  br label %while.cond

while.cond:                                       ; preds = %if.end43, %entry
  %iplus.addr.0 = phi %struct.node* [ %iplus, %entry ], [ %iplus.addr.1, %if.end43 ]
  %jplus.addr.0 = phi %struct.node* [ %jplus, %entry ], [ %jplus.addr.1, %if.end43 ]
  %iminus.0 = phi %struct.node* [ null, %entry ], [ %iminus.9, %if.end43 ]
  %cmp = icmp ne %struct.node* %iplus.addr.0, %jplus.addr.0
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %depth = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 11
  %i = load i64, i64* %depth, align 8
  %depth1 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 11
  %i1 = load i64, i64* %depth1, align 8
  %cmp2 = icmp slt i64 %i, %i1
  br i1 %cmp2, label %if.then, label %if.else19

if.then:                                          ; preds = %while.body
  %orientation = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 1
  %i2 = load i32, i32* %orientation, align 8
  %tobool = icmp ne i32 %i2, 0
  br i1 %tobool, label %if.then3, label %if.else

if.then3:                                         ; preds = %if.then
  %i3 = load i64, i64* %delta, align 8
  %flow = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 10
  %i4 = load i64, i64* %flow, align 8
  %cmp4 = icmp sgt i64 %i3, %i4
  br i1 %cmp4, label %if.then5, label %if.end

if.then5:                                         ; preds = %if.then3
  %flow6 = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 10
  %i5 = load i64, i64* %flow6, align 8
  store i64 %i5, i64* %delta, align 8
  store i64 0, i64* %xchange, align 8
  br label %if.end

if.end:                                           ; preds = %if.then5, %if.then3
  %iminus.1 = phi %struct.node* [ %iplus.addr.0, %if.then5 ], [ %iminus.0, %if.then3 ]
  br label %if.end17

if.else:                                          ; preds = %if.then
  %pred = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 3
  %i6 = load %struct.node*, %struct.node** %pred, align 8
  %pred7 = getelementptr inbounds %struct.node, %struct.node* %i6, i32 0, i32 3
  %i7 = load %struct.node*, %struct.node** %pred7, align 8
  %tobool8 = icmp ne %struct.node* %i7, null
  br i1 %tobool8, label %if.then9, label %if.end16

if.then9:                                         ; preds = %if.else
  %i8 = load i64, i64* %delta, align 8
  %flow10 = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 10
  %i9 = load i64, i64* %flow10, align 8
  %sub = sub nsw i64 1, %i9
  %cmp11 = icmp sgt i64 %i8, %sub
  br i1 %cmp11, label %if.then12, label %if.end15

if.then12:                                        ; preds = %if.then9
  %flow13 = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 10
  %i10 = load i64, i64* %flow13, align 8
  %sub14 = sub nsw i64 1, %i10
  store i64 %sub14, i64* %delta, align 8
  store i64 0, i64* %xchange, align 8
  br label %if.end15

if.end15:                                         ; preds = %if.then12, %if.then9
  %iminus.2 = phi %struct.node* [ %iplus.addr.0, %if.then12 ], [ %iminus.0, %if.then9 ]
  br label %if.end16

if.end16:                                         ; preds = %if.end15, %if.else
  %iminus.3 = phi %struct.node* [ %iminus.2, %if.end15 ], [ %iminus.0, %if.else ]
  br label %if.end17

if.end17:                                         ; preds = %if.end16, %if.end
  %iminus.4 = phi %struct.node* [ %iminus.1, %if.end ], [ %iminus.3, %if.end16 ]
  %pred18 = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 3
  %i11 = load %struct.node*, %struct.node** %pred18, align 8
  br label %if.end43

if.else19:                                        ; preds = %while.body
  %orientation20 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 1
  %i12 = load i32, i32* %orientation20, align 8
  %tobool21 = icmp ne i32 %i12, 0
  br i1 %tobool21, label %if.else28, label %if.then22

if.then22:                                        ; preds = %if.else19
  %i13 = load i64, i64* %delta, align 8
  %flow23 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 10
  %i14 = load i64, i64* %flow23, align 8
  %cmp24 = icmp sge i64 %i13, %i14
  br i1 %cmp24, label %if.then25, label %if.end27

if.then25:                                        ; preds = %if.then22
  %flow26 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 10
  %i15 = load i64, i64* %flow26, align 8
  store i64 %i15, i64* %delta, align 8
  store i64 1, i64* %xchange, align 8
  br label %if.end27

if.end27:                                         ; preds = %if.then25, %if.then22
  %iminus.5 = phi %struct.node* [ %jplus.addr.0, %if.then25 ], [ %iminus.0, %if.then22 ]
  br label %if.end41

if.else28:                                        ; preds = %if.else19
  %pred29 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 3
  %i16 = load %struct.node*, %struct.node** %pred29, align 8
  %pred30 = getelementptr inbounds %struct.node, %struct.node* %i16, i32 0, i32 3
  %i17 = load %struct.node*, %struct.node** %pred30, align 8
  %tobool31 = icmp ne %struct.node* %i17, null
  br i1 %tobool31, label %if.then32, label %if.end40

if.then32:                                        ; preds = %if.else28
  %i18 = load i64, i64* %delta, align 8
  %flow33 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 10
  %i19 = load i64, i64* %flow33, align 8
  %sub34 = sub nsw i64 1, %i19
  %cmp35 = icmp sge i64 %i18, %sub34
  br i1 %cmp35, label %if.then36, label %if.end39

if.then36:                                        ; preds = %if.then32
  %flow37 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 10
  %i20 = load i64, i64* %flow37, align 8
  %sub38 = sub nsw i64 1, %i20
  store i64 %sub38, i64* %delta, align 8
  store i64 1, i64* %xchange, align 8
  br label %if.end39

if.end39:                                         ; preds = %if.then36, %if.then32
  %iminus.6 = phi %struct.node* [ %jplus.addr.0, %if.then36 ], [ %iminus.0, %if.then32 ]
  br label %if.end40

if.end40:                                         ; preds = %if.end39, %if.else28
  %iminus.7 = phi %struct.node* [ %iminus.6, %if.end39 ], [ %iminus.0, %if.else28 ]
  br label %if.end41

if.end41:                                         ; preds = %if.end40, %if.end27
  %iminus.8 = phi %struct.node* [ %iminus.7, %if.end40 ], [ %iminus.5, %if.end27 ]
  %pred42 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 3
  %i21 = load %struct.node*, %struct.node** %pred42, align 8
  br label %if.end43

if.end43:                                         ; preds = %if.end41, %if.end17
  %iplus.addr.1 = phi %struct.node* [ %i11, %if.end17 ], [ %iplus.addr.0, %if.end41 ]
  %jplus.addr.1 = phi %struct.node* [ %jplus.addr.0, %if.end17 ], [ %i21, %if.end41 ]
  %iminus.9 = phi %struct.node* [ %iminus.4, %if.end17 ], [ %iminus.8, %if.end41 ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  store %struct.node* %iplus.addr.0, %struct.node** %w, align 8
  ret %struct.node* %iminus.0
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @primal_update_flow(%struct.node* %iplus, %struct.node* %jplus, %struct.node* %w) #0 {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %iplus.addr.0 = phi %struct.node* [ %iplus, %entry ], [ %i1, %for.inc ]
  %cmp = icmp ne %struct.node* %iplus.addr.0, %w
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %orientation = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 1
  %i = load i32, i32* %orientation, align 8
  %tobool = icmp ne i32 %i, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %for.body
  %flow = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 10
  store i64 0, i64* %flow, align 8
  br label %if.end

if.else:                                          ; preds = %for.body
  %flow1 = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 10
  store i64 1, i64* %flow1, align 8
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %pred = getelementptr inbounds %struct.node, %struct.node* %iplus.addr.0, i32 0, i32 3
  %i1 = load %struct.node*, %struct.node** %pred, align 8
  br label %for.cond

for.end:                                          ; preds = %for.cond
  br label %for.cond2

for.cond2:                                        ; preds = %for.inc12, %for.end
  %jplus.addr.0 = phi %struct.node* [ %jplus, %for.end ], [ %i3, %for.inc12 ]
  %cmp3 = icmp ne %struct.node* %jplus.addr.0, %w
  br i1 %cmp3, label %for.body4, label %for.end14

for.body4:                                        ; preds = %for.cond2
  %orientation5 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 1
  %i2 = load i32, i32* %orientation5, align 8
  %tobool6 = icmp ne i32 %i2, 0
  br i1 %tobool6, label %if.then7, label %if.else9

if.then7:                                         ; preds = %for.body4
  %flow8 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 10
  store i64 1, i64* %flow8, align 8
  br label %if.end11

if.else9:                                         ; preds = %for.body4
  %flow10 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 10
  store i64 0, i64* %flow10, align 8
  br label %if.end11

if.end11:                                         ; preds = %if.else9, %if.then7
  br label %for.inc12

for.inc12:                                        ; preds = %if.end11
  %pred13 = getelementptr inbounds %struct.node, %struct.node* %jplus.addr.0, i32 0, i32 3
  %i3 = load %struct.node*, %struct.node** %pred13, align 8
  br label %for.cond2

for.end14:                                        ; preds = %for.cond2
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local i64 @primal_net_simplex(%struct.network* %net) #0 {
entry:
  %delta = alloca i64, align 8
  %xchange = alloca i64, align 8
  %w = alloca %struct.node*, align 8
  %red_cost_of_bea = alloca i64, align 8
  %arcs1 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 23
  %i = load %struct.arc*, %struct.arc** %arcs1, align 8
  %stop_arcs2 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 24
  %i1 = load %struct.arc*, %struct.arc** %stop_arcs2, align 8
  %m3 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 5
  %i2 = load i64, i64* %m3, align 8
  %iterations4 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 27
  %bound_exchanges5 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 28
  %checksum6 = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 29
  br label %while.cond

while.cond:                                       ; preds = %if.end57, %entry
  %opt.0 = phi i64 [ 0, %entry ], [ %opt.1, %if.end57 ]
  %tobool = icmp ne i64 %opt.0, 0
  %lnot = xor i1 %tobool, true
  br i1 %lnot, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call = call %struct.arc* @primal_bea_mpp(i64 %i2, %struct.arc* %i, %struct.arc* %i1, i64* %red_cost_of_bea)
  %tobool7 = icmp ne %struct.arc* %call, null
  br i1 %tobool7, label %if.then, label %if.else56

if.then:                                          ; preds = %while.body
  %i3 = load i64, i64* %iterations4, align 8
  %inc = add nsw i64 %i3, 1
  store i64 %inc, i64* %iterations4, align 8
  %i4 = load i64, i64* %red_cost_of_bea, align 8
  %cmp = icmp sgt i64 %i4, 0
  br i1 %cmp, label %if.then8, label %if.else

if.then8:                                         ; preds = %if.then
  %head = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 2
  %i5 = load %struct.node*, %struct.node** %head, align 8
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 1
  %i6 = load %struct.node*, %struct.node** %tail, align 8
  br label %if.end

if.else:                                          ; preds = %if.then
  %tail9 = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 1
  %i7 = load %struct.node*, %struct.node** %tail9, align 8
  %head10 = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 2
  %i8 = load %struct.node*, %struct.node** %head10, align 8
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then8
  %jplus.0 = phi %struct.node* [ %i6, %if.then8 ], [ %i8, %if.else ]
  %iplus.0 = phi %struct.node* [ %i5, %if.then8 ], [ %i7, %if.else ]
  store i64 1, i64* %delta, align 8
  %call11 = call %struct.node* @primal_iminus(i64* %delta, i64* %xchange, %struct.node* %iplus.0, %struct.node* %jplus.0, %struct.node** %w)
  %tobool12 = icmp ne %struct.node* %call11, null
  br i1 %tobool12, label %if.else24, label %if.then13

if.then13:                                        ; preds = %if.end
  %i9 = load i64, i64* %bound_exchanges5, align 8
  %inc14 = add nsw i64 %i9, 1
  store i64 %inc14, i64* %bound_exchanges5, align 8
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 3
  %i10 = load i32, i32* %ident, align 8
  %cmp15 = icmp eq i32 %i10, 2
  br i1 %cmp15, label %if.then16, label %if.else18

if.then16:                                        ; preds = %if.then13
  %ident17 = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 3
  store i32 1, i32* %ident17, align 8
  br label %if.end20

if.else18:                                        ; preds = %if.then13
  %ident19 = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 3
  store i32 2, i32* %ident19, align 8
  br label %if.end20

if.end20:                                         ; preds = %if.else18, %if.then16
  %i11 = load i64, i64* %delta, align 8
  %tobool21 = icmp ne i64 %i11, 0
  br i1 %tobool21, label %if.then22, label %if.end23

if.then22:                                        ; preds = %if.end20
  %i12 = load %struct.node*, %struct.node** %w, align 8
  call void @primal_update_flow(%struct.node* %iplus.0, %struct.node* %jplus.0, %struct.node* %i12)
  br label %if.end23

if.end23:                                         ; preds = %if.then22, %if.end20
  br label %if.end55

if.else24:                                        ; preds = %if.end
  %i13 = load i64, i64* %xchange, align 8
  %tobool25 = icmp ne i64 %i13, 0
  br i1 %tobool25, label %if.then26, label %if.end27

if.then26:                                        ; preds = %if.else24
  br label %if.end27

if.end27:                                         ; preds = %if.then26, %if.else24
  %jplus.1 = phi %struct.node* [ %iplus.0, %if.then26 ], [ %jplus.0, %if.else24 ]
  %iplus.1 = phi %struct.node* [ %jplus.0, %if.then26 ], [ %iplus.0, %if.else24 ]
  %pred = getelementptr inbounds %struct.node, %struct.node* %call11, i32 0, i32 3
  %i14 = load %struct.node*, %struct.node** %pred, align 8
  %basic_arc = getelementptr inbounds %struct.node, %struct.node* %call11, i32 0, i32 6
  %i15 = load %struct.arc*, %struct.arc** %basic_arc, align 8
  %i16 = load i64, i64* %xchange, align 8
  %orientation = getelementptr inbounds %struct.node, %struct.node* %call11, i32 0, i32 1
  %i17 = load i32, i32* %orientation, align 8
  %conv = sext i32 %i17 to i64
  %cmp28 = icmp ne i64 %i16, %conv
  br i1 %cmp28, label %if.then30, label %if.else31

if.then30:                                        ; preds = %if.end27
  br label %if.end32

if.else31:                                        ; preds = %if.end27
  br label %if.end32

if.end32:                                         ; preds = %if.else31, %if.then30
  %new_set.0 = phi i64 [ 1, %if.then30 ], [ 2, %if.else31 ]
  %i18 = load i64, i64* %red_cost_of_bea, align 8
  %cmp33 = icmp sgt i64 %i18, 0
  br i1 %cmp33, label %if.then35, label %if.else36

if.then35:                                        ; preds = %if.end32
  %i19 = load i64, i64* %delta, align 8
  %sub = sub nsw i64 1, %i19
  br label %if.end37

if.else36:                                        ; preds = %if.end32
  %i20 = load i64, i64* %delta, align 8
  br label %if.end37

if.end37:                                         ; preds = %if.else36, %if.then35
  %new_flow.0 = phi i64 [ %sub, %if.then35 ], [ %i20, %if.else36 ]
  %tail38 = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 1
  %i21 = load %struct.node*, %struct.node** %tail38, align 8
  %cmp39 = icmp eq %struct.node* %i21, %iplus.1
  br i1 %cmp39, label %if.then41, label %if.else42

if.then41:                                        ; preds = %if.end37
  br label %if.end43

if.else42:                                        ; preds = %if.end37
  br label %if.end43

if.end43:                                         ; preds = %if.else42, %if.then41
  %new_orientation.0 = phi i64 [ 1, %if.then41 ], [ 0, %if.else42 ]
  %i22 = load i64, i64* %xchange, align 8
  %tobool44 = icmp ne i64 %i22, 0
  %lnot45 = xor i1 %tobool44, true
  %lnot.ext = zext i1 %lnot45 to i32
  %conv46 = sext i32 %lnot.ext to i64
  %i23 = load i64, i64* %delta, align 8
  %i24 = load %struct.node*, %struct.node** %w, align 8
  %i25 = load i64, i64* %red_cost_of_bea, align 8
  %feas_tol = getelementptr inbounds %struct.network, %struct.network* %net, i32 0, i32 16
  %i26 = load i64, i64* %feas_tol, align 8
  call void @update_tree(i64 %conv46, i64 %new_orientation.0, i64 %i23, i64 %new_flow.0, %struct.node* %iplus.1, %struct.node* %jplus.1, %struct.node* %call11, %struct.node* %i14, %struct.node* %i24, %struct.arc* %call, i64 %i25, i64 %i26)
  %ident47 = getelementptr inbounds %struct.arc, %struct.arc* %call, i32 0, i32 3
  store i32 0, i32* %ident47, align 8
  %conv48 = trunc i64 %new_set.0 to i32
  %ident49 = getelementptr inbounds %struct.arc, %struct.arc* %i15, i32 0, i32 3
  store i32 %conv48, i32* %ident49, align 8
  %i27 = load i64, i64* %iterations4, align 8
  %sub50 = sub nsw i64 %i27, 1
  %rem = srem i64 %sub50, 200
  %tobool51 = icmp ne i64 %rem, 0
  br i1 %tobool51, label %if.end54, label %if.then52

if.then52:                                        ; preds = %if.end43
  %call53 = call i64 @refresh_potential(%struct.network* %net)
  %i28 = load i64, i64* %checksum6, align 8
  %add = add nsw i64 %i28, %call53
  store i64 %add, i64* %checksum6, align 8
  br label %if.end54

if.end54:                                         ; preds = %if.then52, %if.end43
  br label %if.end55

if.end55:                                         ; preds = %if.end54, %if.end23
  br label %if.end57

if.else56:                                        ; preds = %while.body
  br label %if.end57

if.end57:                                         ; preds = %if.else56, %if.end55
  %opt.1 = phi i64 [ %opt.0, %if.end55 ], [ 1, %if.else56 ]
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %call58 = call i64 @refresh_potential(%struct.network* %net)
  %i29 = load i64, i64* %checksum6, align 8
  %add59 = add nsw i64 %i29, %call58
  store i64 %add59, i64* %checksum6, align 8
  %call60 = call i64 @primal_feasible(%struct.network* %net)
  %call61 = call i64 @dual_feasible(%struct.network* %net)
  ret i64 0
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @bea_is_dual_infeasible(%struct.arc* %arc, i64 %red_cost) #0 {
entry:
  %cmp = icmp slt i64 %red_cost, 0
  br i1 %cmp, label %land.lhs.true, label %lor.rhs

land.lhs.true:                                    ; preds = %entry
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %arc, i32 0, i32 3
  %i = load i32, i32* %ident, align 8
  %cmp1 = icmp eq i32 %i, 1
  br i1 %cmp1, label %lor.end, label %lor.rhs

lor.rhs:                                          ; preds = %land.lhs.true, %entry
  %cmp2 = icmp sgt i64 %red_cost, 0
  br i1 %cmp2, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %lor.rhs
  %ident3 = getelementptr inbounds %struct.arc, %struct.arc* %arc, i32 0, i32 3
  %i1 = load i32, i32* %ident3, align 8
  %cmp4 = icmp eq i32 %i1, 2
  br label %land.end

land.end:                                         ; preds = %land.rhs, %lor.rhs
  %i2 = phi i1 [ false, %lor.rhs ], [ %cmp4, %land.rhs ]
  br label %lor.end

lor.end:                                          ; preds = %land.end, %land.lhs.true
  %i3 = phi i1 [ true, %land.lhs.true ], [ %i2, %land.end ]
  %lor.ext = zext i1 %i3 to i32
  ret i32 %lor.ext
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @sort_basket(i64 %min, i64 %max) #0 {
entry:
  %add = add nsw i64 %min, %max
  %div = sdiv i64 %add, 2
  %arrayidx = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %div
  %i = load %struct.basket*, %struct.basket** %arrayidx, align 8
  %abs_cost = getelementptr inbounds %struct.basket, %struct.basket* %i, i32 0, i32 2
  %i1 = load i64, i64* %abs_cost, align 8
  br label %do.body

do.body:                                          ; preds = %do.cond, %entry
  %l.0 = phi i64 [ %min, %entry ], [ %l.2, %do.cond ]
  %r.0 = phi i64 [ %max, %entry ], [ %r.2, %do.cond ]
  br label %while.cond

while.cond:                                       ; preds = %while.body, %do.body
  %l.1 = phi i64 [ %l.0, %do.body ], [ %inc, %while.body ]
  %arrayidx1 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %l.1
  %i2 = load %struct.basket*, %struct.basket** %arrayidx1, align 8
  %abs_cost2 = getelementptr inbounds %struct.basket, %struct.basket* %i2, i32 0, i32 2
  %i3 = load i64, i64* %abs_cost2, align 8
  %cmp = icmp sgt i64 %i3, %i1
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %inc = add nsw i64 %l.1, 1
  br label %while.cond

while.end:                                        ; preds = %while.cond
  br label %while.cond3

while.cond3:                                      ; preds = %while.body7, %while.end
  %r.1 = phi i64 [ %r.0, %while.end ], [ %dec, %while.body7 ]
  %arrayidx4 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %r.1
  %i4 = load %struct.basket*, %struct.basket** %arrayidx4, align 8
  %abs_cost5 = getelementptr inbounds %struct.basket, %struct.basket* %i4, i32 0, i32 2
  %i5 = load i64, i64* %abs_cost5, align 8
  %cmp6 = icmp sgt i64 %i1, %i5
  br i1 %cmp6, label %while.body7, label %while.end8

while.body7:                                      ; preds = %while.cond3
  %dec = add nsw i64 %r.1, -1
  br label %while.cond3

while.end8:                                       ; preds = %while.cond3
  %cmp9 = icmp slt i64 %l.1, %r.1
  br i1 %cmp9, label %if.then, label %if.end

if.then:                                          ; preds = %while.end8
  %arrayidx10 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %l.1
  %i6 = load %struct.basket*, %struct.basket** %arrayidx10, align 8
  %arrayidx11 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %r.1
  %i7 = load %struct.basket*, %struct.basket** %arrayidx11, align 8
  %arrayidx12 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %l.1
  store %struct.basket* %i7, %struct.basket** %arrayidx12, align 8
  %arrayidx13 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %r.1
  store %struct.basket* %i6, %struct.basket** %arrayidx13, align 8
  br label %if.end

if.end:                                           ; preds = %if.then, %while.end8
  %cmp14 = icmp sle i64 %l.1, %r.1
  br i1 %cmp14, label %if.then15, label %if.end18

if.then15:                                        ; preds = %if.end
  %inc16 = add nsw i64 %l.1, 1
  %dec17 = add nsw i64 %r.1, -1
  br label %if.end18

if.end18:                                         ; preds = %if.then15, %if.end
  %l.2 = phi i64 [ %inc16, %if.then15 ], [ %l.1, %if.end ]
  %r.2 = phi i64 [ %dec17, %if.then15 ], [ %r.1, %if.end ]
  br label %do.cond

do.cond:                                          ; preds = %if.end18
  %cmp19 = icmp sle i64 %l.2, %r.2
  br i1 %cmp19, label %do.body, label %do.end

do.end:                                           ; preds = %do.cond
  %cmp20 = icmp slt i64 %min, %r.2
  br i1 %cmp20, label %if.then21, label %if.end22

if.then21:                                        ; preds = %do.end
  call void @sort_basket(i64 %min, i64 %r.2)
  br label %if.end22

if.end22:                                         ; preds = %if.then21, %do.end
  %cmp23 = icmp slt i64 %l.2, %max
  br i1 %cmp23, label %land.lhs.true, label %if.end26

land.lhs.true:                                    ; preds = %if.end22
  %cmp24 = icmp sle i64 %l.2, 50
  br i1 %cmp24, label %if.then25, label %if.end26

if.then25:                                        ; preds = %land.lhs.true
  call void @sort_basket(i64 %l.2, i64 %max)
  br label %if.end26

if.end26:                                         ; preds = %if.then25, %land.lhs.true, %if.end22
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local %struct.arc* @primal_bea_mpp(i64 %m, %struct.arc* %arcs, %struct.arc* %stop_arcs, i64* %red_cost_of_bea) #0 {
entry:
  %i = load i64, i64* @initialize, align 8
  %tobool = icmp ne i64 %i, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %if.then
  %i.0 = phi i64 [ 1, %if.then ], [ %inc, %for.inc ]
  %cmp = icmp slt i64 %i.0, 351
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %arrayidx = getelementptr inbounds [351 x %struct.basket], [351 x %struct.basket]* @basket, i64 0, i64 %i.0
  %arrayidx1 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %i.0
  store %struct.basket* %arrayidx, %struct.basket** %arrayidx1, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i64 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %sub = sub nsw i64 %m, 1
  %div = sdiv i64 %sub, 300
  %add = add nsw i64 %div, 1
  store i64 %add, i64* @nr_group, align 8
  store i64 0, i64* @group_pos, align 8
  store i64 0, i64* @basket_size, align 8
  store i64 0, i64* @initialize, align 8
  br label %if.end28

if.else:                                          ; preds = %entry
  br label %for.cond2

for.cond2:                                        ; preds = %for.inc25, %if.else
  %i.1 = phi i64 [ 2, %if.else ], [ %inc26, %for.inc25 ]
  %next.0 = phi i64 [ 0, %if.else ], [ %next.1, %for.inc25 ]
  %cmp3 = icmp sle i64 %i.1, 50
  br i1 %cmp3, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %for.cond2
  %i1 = load i64, i64* @basket_size, align 8
  %cmp4 = icmp sle i64 %i.1, %i1
  br label %land.end

land.end:                                         ; preds = %land.rhs, %for.cond2
  %i2 = phi i1 [ false, %for.cond2 ], [ %cmp4, %land.rhs ]
  br i1 %i2, label %for.body5, label %for.end27

for.body5:                                        ; preds = %land.end
  %arrayidx6 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %i.1
  %i3 = load %struct.basket*, %struct.basket** %arrayidx6, align 8
  %a = getelementptr inbounds %struct.basket, %struct.basket* %i3, i32 0, i32 0
  %i4 = load %struct.arc*, %struct.arc** %a, align 8
  %cost = getelementptr inbounds %struct.arc, %struct.arc* %i4, i32 0, i32 0
  %i5 = load i64, i64* %cost, align 8
  %tail = getelementptr inbounds %struct.arc, %struct.arc* %i4, i32 0, i32 1
  %i6 = load %struct.node*, %struct.node** %tail, align 8
  %potential = getelementptr inbounds %struct.node, %struct.node* %i6, i32 0, i32 0
  %i7 = load i64, i64* %potential, align 8
  %sub7 = sub nsw i64 %i5, %i7
  %head = getelementptr inbounds %struct.arc, %struct.arc* %i4, i32 0, i32 2
  %i8 = load %struct.node*, %struct.node** %head, align 8
  %potential8 = getelementptr inbounds %struct.node, %struct.node* %i8, i32 0, i32 0
  %i9 = load i64, i64* %potential8, align 8
  %add9 = add nsw i64 %sub7, %i9
  %cmp10 = icmp slt i64 %add9, 0
  br i1 %cmp10, label %land.lhs.true, label %lor.lhs.false

land.lhs.true:                                    ; preds = %for.body5
  %ident = getelementptr inbounds %struct.arc, %struct.arc* %i4, i32 0, i32 3
  %i10 = load i32, i32* %ident, align 8
  %cmp11 = icmp eq i32 %i10, 1
  br i1 %cmp11, label %if.then16, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %land.lhs.true, %for.body5
  %cmp12 = icmp sgt i64 %add9, 0
  br i1 %cmp12, label %land.lhs.true13, label %if.end

land.lhs.true13:                                  ; preds = %lor.lhs.false
  %ident14 = getelementptr inbounds %struct.arc, %struct.arc* %i4, i32 0, i32 3
  %i11 = load i32, i32* %ident14, align 8
  %cmp15 = icmp eq i32 %i11, 2
  br i1 %cmp15, label %if.then16, label %if.end

if.then16:                                        ; preds = %land.lhs.true13, %land.lhs.true
  %inc17 = add nsw i64 %next.0, 1
  %arrayidx18 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %inc17
  %i12 = load %struct.basket*, %struct.basket** %arrayidx18, align 8
  %a19 = getelementptr inbounds %struct.basket, %struct.basket* %i12, i32 0, i32 0
  store %struct.arc* %i4, %struct.arc** %a19, align 8
  %arrayidx20 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %inc17
  %i13 = load %struct.basket*, %struct.basket** %arrayidx20, align 8
  %cost21 = getelementptr inbounds %struct.basket, %struct.basket* %i13, i32 0, i32 1
  store i64 %add9, i64* %cost21, align 8
  %cmp22 = icmp sge i64 %add9, 0
  br i1 %cmp22, label %cond.true, label %cond.false

cond.true:                                        ; preds = %if.then16
  br label %cond.end

cond.false:                                       ; preds = %if.then16
  %sub23 = sub nsw i64 0, %add9
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i64 [ %add9, %cond.true ], [ %sub23, %cond.false ]
  %arrayidx24 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %inc17
  %i14 = load %struct.basket*, %struct.basket** %arrayidx24, align 8
  %abs_cost = getelementptr inbounds %struct.basket, %struct.basket* %i14, i32 0, i32 2
  store i64 %cond, i64* %abs_cost, align 8
  br label %if.end

if.end:                                           ; preds = %cond.end, %land.lhs.true13, %lor.lhs.false
  %next.1 = phi i64 [ %inc17, %cond.end ], [ %next.0, %land.lhs.true13 ], [ %next.0, %lor.lhs.false ]
  br label %for.inc25

for.inc25:                                        ; preds = %if.end
  %inc26 = add nsw i64 %i.1, 1
  br label %for.cond2

for.end27:                                        ; preds = %land.end
  store i64 %next.0, i64* @basket_size, align 8
  br label %if.end28

if.end28:                                         ; preds = %for.end27, %for.end
  %i15 = load i64, i64* @group_pos, align 8
  br label %NEXT

NEXT:                                             ; preds = %if.then69, %if.end28
  %i16 = load i64, i64* @group_pos, align 8
  %add.ptr = getelementptr inbounds %struct.arc, %struct.arc* %arcs, i64 %i16
  br label %for.cond29

for.cond29:                                       ; preds = %for.inc59, %NEXT
  %arc.0 = phi %struct.arc* [ %add.ptr, %NEXT ], [ %add.ptr60, %for.inc59 ]
  %cmp30 = icmp ult %struct.arc* %arc.0, %stop_arcs
  br i1 %cmp30, label %for.body31, label %for.end61

for.body31:                                       ; preds = %for.cond29
  %ident32 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 3
  %i17 = load i32, i32* %ident32, align 8
  %cmp33 = icmp sgt i32 %i17, 0
  br i1 %cmp33, label %if.then34, label %if.end58

if.then34:                                        ; preds = %for.body31
  %cost35 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 0
  %i18 = load i64, i64* %cost35, align 8
  %tail36 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 1
  %i19 = load %struct.node*, %struct.node** %tail36, align 8
  %potential37 = getelementptr inbounds %struct.node, %struct.node* %i19, i32 0, i32 0
  %i20 = load i64, i64* %potential37, align 8
  %sub38 = sub nsw i64 %i18, %i20
  %head39 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i32 0, i32 2
  %i21 = load %struct.node*, %struct.node** %head39, align 8
  %potential40 = getelementptr inbounds %struct.node, %struct.node* %i21, i32 0, i32 0
  %i22 = load i64, i64* %potential40, align 8
  %add41 = add nsw i64 %sub38, %i22
  %call = call i32 @bea_is_dual_infeasible(%struct.arc* %arc.0, i64 %add41)
  %tobool42 = icmp ne i32 %call, 0
  br i1 %tobool42, label %if.then43, label %if.end57

if.then43:                                        ; preds = %if.then34
  %i23 = load i64, i64* @basket_size, align 8
  %inc44 = add nsw i64 %i23, 1
  store i64 %inc44, i64* @basket_size, align 8
  %i24 = load i64, i64* @basket_size, align 8
  %arrayidx45 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %i24
  %i25 = load %struct.basket*, %struct.basket** %arrayidx45, align 8
  %a46 = getelementptr inbounds %struct.basket, %struct.basket* %i25, i32 0, i32 0
  store %struct.arc* %arc.0, %struct.arc** %a46, align 8
  %i26 = load i64, i64* @basket_size, align 8
  %arrayidx47 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %i26
  %i27 = load %struct.basket*, %struct.basket** %arrayidx47, align 8
  %cost48 = getelementptr inbounds %struct.basket, %struct.basket* %i27, i32 0, i32 1
  store i64 %add41, i64* %cost48, align 8
  %cmp49 = icmp sge i64 %add41, 0
  br i1 %cmp49, label %cond.true50, label %cond.false51

cond.true50:                                      ; preds = %if.then43
  br label %cond.end53

cond.false51:                                     ; preds = %if.then43
  %sub52 = sub nsw i64 0, %add41
  br label %cond.end53

cond.end53:                                       ; preds = %cond.false51, %cond.true50
  %cond54 = phi i64 [ %add41, %cond.true50 ], [ %sub52, %cond.false51 ]
  %i28 = load i64, i64* @basket_size, align 8
  %arrayidx55 = getelementptr inbounds [351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 %i28
  %i29 = load %struct.basket*, %struct.basket** %arrayidx55, align 8
  %abs_cost56 = getelementptr inbounds %struct.basket, %struct.basket* %i29, i32 0, i32 2
  store i64 %cond54, i64* %abs_cost56, align 8
  br label %if.end57

if.end57:                                         ; preds = %cond.end53, %if.then34
  br label %if.end58

if.end58:                                         ; preds = %if.end57, %for.body31
  br label %for.inc59

for.inc59:                                        ; preds = %if.end58
  %i30 = load i64, i64* @nr_group, align 8
  %add.ptr60 = getelementptr inbounds %struct.arc, %struct.arc* %arc.0, i64 %i30
  br label %for.cond29

for.end61:                                        ; preds = %for.cond29
  %i31 = load i64, i64* @group_pos, align 8
  %inc62 = add nsw i64 %i31, 1
  store i64 %inc62, i64* @group_pos, align 8
  %i32 = load i64, i64* @nr_group, align 8
  %cmp63 = icmp eq i64 %inc62, %i32
  br i1 %cmp63, label %if.then64, label %if.end65

if.then64:                                        ; preds = %for.end61
  store i64 0, i64* @group_pos, align 8
  br label %if.end65

if.end65:                                         ; preds = %if.then64, %for.end61
  %i33 = load i64, i64* @basket_size, align 8
  %cmp66 = icmp slt i64 %i33, 50
  br i1 %cmp66, label %land.lhs.true67, label %if.end70

land.lhs.true67:                                  ; preds = %if.end65
  %i34 = load i64, i64* @group_pos, align 8
  %cmp68 = icmp ne i64 %i34, %i15
  br i1 %cmp68, label %if.then69, label %if.end70

if.then69:                                        ; preds = %land.lhs.true67
  br label %NEXT

if.end70:                                         ; preds = %land.lhs.true67, %if.end65
  %i35 = load i64, i64* @basket_size, align 8
  %cmp71 = icmp eq i64 %i35, 0
  br i1 %cmp71, label %if.then72, label %if.end73

if.then72:                                        ; preds = %if.end70
  store i64 1, i64* @initialize, align 8
  store i64 0, i64* %red_cost_of_bea, align 8
  br label %return

if.end73:                                         ; preds = %if.end70
  %i36 = load i64, i64* @basket_size, align 8
  call void @sort_basket(i64 1, i64 %i36)
  %i37 = load %struct.basket*, %struct.basket** getelementptr inbounds ([351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 1), align 8
  %cost74 = getelementptr inbounds %struct.basket, %struct.basket* %i37, i32 0, i32 1
  %i38 = load i64, i64* %cost74, align 8
  store i64 %i38, i64* %red_cost_of_bea, align 8
  %i39 = load %struct.basket*, %struct.basket** getelementptr inbounds ([351 x %struct.basket*], [351 x %struct.basket*]* @perm, i64 0, i64 1), align 8
  %a75 = getelementptr inbounds %struct.basket, %struct.basket* %i39, i32 0, i32 0
  %i40 = load %struct.arc*, %struct.arc** %a75, align 8
  br label %return

return:                                           ; preds = %if.end73, %if.then72
  %retval.0 = phi %struct.arc* [ null, %if.then72 ], [ %i40, %if.end73 ]
  ret %struct.arc* %retval.0
}

attributes #0 = { noinline nounwind uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nofree nosync nounwind willreturn writeonly }
attributes #4 = { nounwind "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { argmemonly nofree nosync nounwind willreturn }
attributes #6 = { noreturn nounwind }
attributes #7 = { nounwind }

!llvm.ident = !{!0, !0, !0, !0, !0, !0, !0, !0, !0, !0, !0}
!llvm.module.flags = !{!1}

!0 = !{!"Ubuntu clang version 12.0.1-8build1"}
!1 = !{i32 1, !"wchar_size", i32 4}
