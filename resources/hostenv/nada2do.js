// this is to set a default value of global function pointeres
// so that they don't ever receive "Undefind"

(function (global) {
    global.__default_nd2 = function (){
        var msg = "done";
        return msg;
    }
})(this);
