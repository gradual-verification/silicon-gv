package viper.silicon.state

sealed trait LoopPosition

object LoopPosition {
  final case object Before extends LoopPosition
  final case object After extends LoopPosition
  final case object Beginning extends LoopPosition
  final case object End extends LoopPosition
}
