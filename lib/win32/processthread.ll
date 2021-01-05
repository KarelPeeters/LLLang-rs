extern fun _ExitProcess@4(exitCode: int);

extern fun _CreateThread@24(
  lpThreadAttributes: &void,
  dwStackSize: int,
  lpStartAddress: (&int) -> int,
  lpParameter: &int,
  dwCreationFlags: int,
  lpThreadI: &int,
) -> int;
