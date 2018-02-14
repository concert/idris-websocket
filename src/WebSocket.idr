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

data JsPtr : String -> Type where
  MkJsPtr : Ptr -> JsPtr x

jsPtr : JsPtr x -> Ptr
jsPtr (MkJsPtr ptr) = ptr

Event : Type
Event = JsPtr "Event"

MkEvent : Ptr -> Event
MkEvent = MkJsPtr

WebSocket : Type
WebSocket = JsPtr "WebSocket"

MkWebSocket : Ptr -> WebSocket
MkWebSocket = MkJsPtr

namespace websocket
  new : Url -> JS_IO WebSocket
  new url = MkWebSocket <$> jscall "new WebSocket(%0)" (String -> JS_IO Ptr) (cast url)

  onOpen : WebSocket -> (String -> JS_IO ()) -> JS_IO ()
  onOpen ws f =
    jscall "%0.onopen = %1" (Ptr -> JsFn (String -> JS_IO ()) -> JS_IO ())
    (jsPtr ws) (MkJsFn f)

  onError : ()
  onError = ?onErrorRHS

  send : WebSocket -> String -> JS_IO ()
  send ws = jscall "%0.send(%1)" (Ptr -> String -> JS_IO ()) (jsPtr ws)

  onMessage : WebSocket -> (String -> JS_IO ()) -> JS_IO ()
  onMessage ws f =
    jscall "%0.onmessage = function(event){%1(event.data)}" (Ptr -> JsFn (String -> JS_IO ()) -> JS_IO ())
    (jsPtr ws) (MkJsFn f)

  onClose : WebSocket -> (Ptr -> JS_IO ()) -> JS_IO ()
  onClose ws f = jscall "%0.onclose = %1" (Ptr -> JsFn (Ptr -> JS_IO ()) -> JS_IO ())
    (jsPtr ws) (MkJsFn f)

  close : WebSocket -> JS_IO ()
  close = jscall "%0.close()" (Ptr -> JS_IO ()) . jsPtr

consoleLog : String -> JS_IO ()
consoleLog = jscall "console.log(%0)" (String -> JS_IO ())

consoleLog' : JsPtr x -> JS_IO ()
consoleLog' = jscall "console.log(%0)" (Ptr -> JS_IO ()) . jsPtr
