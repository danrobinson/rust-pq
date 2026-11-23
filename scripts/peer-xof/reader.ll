B0:
v0 = alloca [136 x i8], align $ALIGN
call void @llvm.lifetime.start.p0(ptr nonnull v0)
v1 = getelementptr inbounds nuw i8, ptr v0, i64 1
call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(135) v1, i8 0, i64 135, i1 false)
store i8 -120, ptr v0, align $ALIGN
v2 = urem i64 length, 136
v3 = sub nuw nsw i64 length, v2
v4 = getelementptr inbounds nuw i8, ptr out, i64 v3
v5 = icmp samesign ult i64 length, 136
br i1 v5, label B2, label B1
B1:
v6 = phi ptr [ v7, B1 ], [ out, B0 ]
v7 = getelementptr inbounds nuw i8, ptr v6, i64 136
tail call void produce(ptr noundef nonnull dereferenceable(136) v6)
v8 = icmp eq ptr v7, v4
br i1 v8, label B2, label B1
B2:
v9 = icmp eq i64 v2, 0
br i1 v9, label B4, label B3
B3:
call void produce(ptr noundef nonnull dereferenceable(136) v0)
call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 v4, ptr nonnull readonly align $ALIGN dereferenceable(136) v0, i64 range(i64 0, -9223372036854775808) v2, i1 false)
br label B4
B4:
call void @llvm.lifetime.end.p0(ptr nonnull v0)
ret void
