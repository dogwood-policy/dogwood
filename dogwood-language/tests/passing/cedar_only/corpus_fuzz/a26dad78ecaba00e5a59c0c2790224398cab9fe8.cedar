permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("ff00:0:ff:55b0:b0b0:b0b0:0b0:65544")) else (ip("::330:3333:3333:3333"))).isMulticast()))
};
