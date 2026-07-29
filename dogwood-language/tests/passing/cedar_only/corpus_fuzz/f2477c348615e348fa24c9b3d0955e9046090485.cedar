permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("3ff:5b40:1dff:ÿe3a:999:b0:b0b0ÿ6544/119")) else (ip("55b0:b0b0:b064:6464:6464:6464:6464:3ff/"))).isMulticast()))
};
