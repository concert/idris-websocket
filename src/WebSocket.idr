module WebSocket

%access export

%inline
jscall : (name : String) -> (ty : Type) -> {auto fty : FTy FFI_JS [] ty} -> ty
jscall name ty = foreign FFI_JS name ty

record Url where
  constructor MkUrl
  urlScheme : String
  urlHost : String

Show Url where
  show url = urlScheme url ++ "://" ++ urlHost url

Cast Url String where
  cast = show

Protocol : Type
Protocol = String

record Event where
  constructor MkEvent
  ePtr : Ptr

public export
record WebSocket where
  constructor MkWebSocket
  wsPtr : Ptr

namespace websocket
  new : Url -> JS_IO WebSocket
  new url = MkWebSocket <$> jscall "new WebSocket(%0)" (String -> JS_IO Ptr) (cast url)

  onOpen : WebSocket -> (String -> JS_IO ()) -> JS_IO ()
  onOpen ws f =
    jscall "%0.onopen = %1" (Ptr -> JsFn (String -> JS_IO ()) -> JS_IO ())
    (wsPtr ws) (MkJsFn f)

  onError : ()
  onError = ?onErrorRHS

  send : WebSocket -> String -> JS_IO ()
  send ws = jscall "%0.send(%1)" (Ptr -> String -> JS_IO ()) (wsPtr ws)

  onMessage : WebSocket -> (String -> JS_IO ()) -> JS_IO ()
  onMessage ws f =
    jscall "%0.onmessage = function(event){%1(event.data)}" (Ptr -> JsFn (String -> JS_IO ()) -> JS_IO ())
    (wsPtr ws) (MkJsFn f)

  onClose : WebSocket -> (Ptr -> JS_IO ()) -> JS_IO ()
  onClose ws f = jscall "%0.onclose = %1" (Ptr -> JsFn (Ptr -> JS_IO ()) -> JS_IO ())
    (wsPtr ws) (MkJsFn f)

  close : WebSocket -> JS_IO ()
  close = jscall "%0.close()" (Ptr -> JS_IO ()) . wsPtr

consoleLog : String -> JS_IO ()
consoleLog = jscall "console.log(%0)" (String -> JS_IO ())

consoleLog' : Ptr -> JS_IO ()
consoleLog' = jscall "console.log(%0)" (Ptr -> JS_IO ())
