from argparse import ArgumentParser

if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument("--INLST", help="Display all the instructions", action="store_true")
    parser.add_argument("--SLV", help="Strong Livness Analysis", action="store_true")
    parser.add_argument("--PTA", help="Pointer Analysis", action="store_true")
    parser.add_argument("--LFCPA", help="Liveness-based Pointer Analysis", action="store_true")
    parser.add_argument("--RVINS", help="Display relevant LLVM IR instructions only", action="store_true")
    parser.add_argument("--SKINS", help="Display skipped LLVM IR instructions only", action="store_true")
    parser.add_argument("--PRINT", help="Print all", action="store_true")
    parser.add_argument("--TRACE", help="Trace the flow of function execution", action="store_true")
    res = parser.parse_args()

    Result = " "

    if res.INLST:
        Result += "GLB_INSLST "
	
    if res.SLV:
        Result += "SLV "

    if res.PTA:
        Result += "PTA "

    if res.LFCPA:
        Result += "RES_LFCPA "

    if res.RVINS:
        Result += "RELV_INS "

    if res.SKINS:
        Result += "SKIP_INS "

    if res.PRINT:
        Result += "PRINT "

    if res.TRACE:
        Result += "TRACE "

    print(Result)
