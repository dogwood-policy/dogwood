forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ((if ([{"": ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")}, {"": ip("4747:4747:4747:4747:4747:4747:ffff:ffff/71")}, {"": ip("58.58.58.138")}].contains({"": ip("::ffff:ffff:ffff:ffff:ffff")})) then [{"": {"": {"": (-8463800222054970742)}}}, {"": {"": {"": (-8463800222054970742)}}}] else [{"": {"": {"": (-8463800222054970742)}}}, {"": {"": {"": (-8463800222054970742)}}}]).contains(context))) && false) && false
};
