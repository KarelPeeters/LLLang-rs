extern fun _WaitForSingleObject@8(
  hHandle: int,
  dwMilliseconds: int,
) -> int;

extern fun _WaitForMultipleObjects@16(
  nCount: int,
  lpHandles: &int,
  bWaitAll: bool,
  dwMilliseconds: int,
) -> int;