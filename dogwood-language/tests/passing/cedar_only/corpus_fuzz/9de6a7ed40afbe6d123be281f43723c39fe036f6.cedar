@UAAAAA("IIII")
permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("0:10e:ff00:0:ff:55b0:b0b0:b0b0")) else (ip(":::ffff:255.255.255.255"))).isMulticast()))
};
