@riTmCm("")
forbid(
  principal is r,
  action in [],
  resource == W::""
) when {
  false && (r::"" is r)
};
