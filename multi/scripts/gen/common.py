SETS = [('128s',16,'SHA2_128S',7856),('128f',16,'SHA2_128F',17088),('192s',24,'SHA2_192S',16224),
        ('192f',24,'SHA2_192F',35664),('256s',32,'SHA2_256S',29792),('256f',32,'SHA2_256F',49856)]
only = sys.argv[1:]
def sets(): return [s for s in SETS if not only or s[0] in only]
def sub(t, rep):
    for k,v in rep.items(): t = t.replace('{'+k+'}', str(v))
    return t
def reps(S,N,SU,SIG):
    sl = 152 if N==16 else 304
    return dict(S=S,N=N,SU=SU,SK=4*N,PK=2*N,SEED=3*N,SL=sl,SLP=sl+257,SIG=SIG)
