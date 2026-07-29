permit(
  principal is a in a::"",
  action,
  resource == a::""
) when {
  (true && (((if true then {"\u{1}+\u{15}": resource} else {"\u{1}+\u{15}": action})["\u{1}+\u{15}"]) has "")) && false
};
