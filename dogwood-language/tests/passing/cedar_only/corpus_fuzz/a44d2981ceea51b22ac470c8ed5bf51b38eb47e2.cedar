@r("")
permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (!((if false then (ip("ffff:ffff:ffb0:b0b0:b020:6e61:6962:6544/126")) else (ip("ccb0:ffff:ffff:ffff:ffff:ffff:ffff:fff"))).isMulticast(context["qqqqqqqqqqaqqqqqqq\u{1}\u{4}qqCfqqqqqqqqް"])))
};
