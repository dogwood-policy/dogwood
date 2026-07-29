permit(
  principal,
  action == Action::"action",
  resource in a::""
) when {
  (true && (if (({"": resource}[""]).getTag({"": ""}[""])) then (if (principal.getTag("")) then (principal.getTag("")) else (resource in action)) else false)) && false
};
