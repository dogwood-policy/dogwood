permit(
  principal == a::"",
  action == Action::":~",
  resource
) when {
  (true && ((({"": {"^": decimal("102601653073870.8227")}}[""])["^"]).lessThan(decimal(principal.getTag("\0\u{10}"))))) && true
};
