forbid(
  principal,
  action,
  resource
) when {
  true && ((if ((ip("::ff:ff27:2782:8202")).isMulticast()) then context else context)[""])
};
