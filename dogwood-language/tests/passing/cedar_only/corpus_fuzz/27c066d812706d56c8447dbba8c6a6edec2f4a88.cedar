@A("")
@L("")
forbid(
  principal,
  action in [Action::"action"],
  resource == a::"@0\0\0+\0\0\0\0\0\0\0\0..B..:...@\0\0\0\0\0"
) when {
  false
};
