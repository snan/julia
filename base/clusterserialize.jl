# This file is a part of Julia. License is MIT: http://julialang.org/license

import .Serializer: known_object_data, object_number, serialize_cycle, deserialize_cycle, writetag,
                      __deserialized_types__, serialize_typename, deserialize_typename,
                      TYPENAME_TAG, GLOBALREF_TAG, object_numbers,
                      serialize_global_from_main, deserialize_global_from_main

type ClusterSerializer{I<:IO} <: AbstractSerializer
    io::I
    counter::Int
    table::ObjectIdDict

    pid::Int                  # Worker we are connected to.
    sent_objects::Set{UInt64} # used by serialize (track objects sent)
    sent_globals::Dict

    ClusterSerializer(io::I) = new(io, 0, ObjectIdDict(),
                                Base.worker_id_from_socket(io),
                                Set{UInt64}(), Dict())
end
ClusterSerializer(io::IO) = ClusterSerializer{typeof(io)}(io)

function deserialize(s::ClusterSerializer, ::Type{TypeName})
    full_body_sent = deserialize(s)
    number = read(s.io, UInt64)
    if !full_body_sent
        tn = get(known_object_data, number, nothing)::TypeName
        if !haskey(object_numbers, tn)
            # set up reverse mapping for serialize
            object_numbers[tn] = number
        end
        deserialize_cycle(s, tn)
    else
        tn = deserialize_typename(s, number)
    end
    return tn
end

function serialize(s::ClusterSerializer, t::TypeName)
    serialize_cycle(s, t) && return
    writetag(s.io, TYPENAME_TAG)

    identifier = object_number(t)
    send_whole = !(identifier in s.sent_objects)
    serialize(s, send_whole)
    write(s.io, identifier)
    if send_whole
        serialize_typename(s, t)
        push!(s.sent_objects, identifier)
    end
#   #println(t.module, ":", t.name, ", id:", identifier, send_whole ? " sent" : " NOT sent")
    nothing
end

const FLG_SER_VAL = UInt8(1)
const FLG_ISCONST_VAL = UInt8(2)
isflagged(v, flg) = (v & flg == flg)

# We will send/resend a global object if
# a) has not been sent previously, i.e., we are seeing this object_id for the
#    for the first time, or,
# b) hash value has changed

function serialize_global_from_main(s::ClusterSerializer, g::GlobalRef)
    v = getfield(Main, g.name)
    println(g)

    serialize(s, g.name)

    flags = UInt8(0)
    if isbits(v)
        flags = flags | FLG_SER_VAL
    else
        oid = object_id(v)
        if haskey(s.sent_globals, oid)
            # We have sent this object before, see if it has changed.
            prev_hash = s.sent_globals[oid]
            new_hash = hash(v)
            if new_hash != prev_hash
                flags = flags | FLG_SER_VAL
                s.sent_globals[oid] = new_hash

                # No need to setup a new finalizer as only the hash
                # value and not the object itself has changed.
            end
        else
            flags = flags | FLG_SER_VAL
            try
                finalizer(v, x->delete_global_tracker(s,x))
                s.sent_globals[oid] = hash(v)
            catch ex
                # Do not track objects that cannot be finalized.
            end
        end
    end
    isconst(Main, g.name) && (flags = flags | FLG_ISCONST_VAL)

    write(s.io, flags)
    isflagged(flags, FLG_SER_VAL) && serialize(s, v)
end

function deserialize_global_from_main(s::ClusterSerializer)
    sym = deserialize(s)::Symbol
    flags = read(s.io, UInt8)

    if isflagged(flags, FLG_SER_VAL)
        v = deserialize(s)
    end

    # create/update binding under Main only if the value has been sent
    if isflagged(flags, FLG_SER_VAL)
        if isflagged(flags, FLG_ISCONST_VAL)
            eval(Main, :(const $sym = $v))
        else
            eval(Main, :($sym = $v))
        end
    end

    return GlobalRef(Main, sym)
end

function delete_global_tracker(s::ClusterSerializer, v)
    oid = object_id(v)
    if haskey(s.sent_globals, oid)
        delete!(s.sent_globals, oid)
    end

    # TODO: Should release memory from the remote nodes.
end

