open util/boolean

abstract sig Profile{
	name:one Name
}

sig PersonalProfile extends Profile{
	//username:one Username,
	eMail:one EMail,
	friends:set PersonalProfile,
	following:set Profile,

	posted: set Content
}

sig Name{}
fact unique_names{all disjoint p,q:Profile | p.name != q.name}
//TODO fact: no name without connection to Profile
sig EMail{}
fact unique_Emails{all disjoint p,q:PersonalProfile | p.eMail != q.eMail}
//fact no_eMail_without_connection{all e:EMail, p:Profile | e = p.eMail}

fact no_reflexiv_friends{all p:Profile | not p in p.friends} 
fact no_reflexiv_followers{all p:Profile | not p in p.following}

sig GroupProfile extends Profile {
	member:set PersonalProfile
}

sig Content{
	visible: Bool
}
fact unique_posts{all disjoint p,q:PersonalProfile, c:Content | c in p.posted => not c in q.posted}
//fact no_post_without_connection{all c:Content,p:Profile | c in p.posted}

abstract sig CommentableContent extends Content{}
abstract sig PersonalContent extends Content{}

sig Photo extends CommentableContent{}
sig Post extends CommentableContent{
	post: String,
	link: some Photo //how do you model 0-several photos? (0..*)
}
sig comment extends CommentableContent{
	comment: String,
	refersTo: some CommentableContent //0..*
}

sig personalMessage extends PersonalContent{
	message: String,
	includedPhoto: lone Photo 	
}
sig personalDetails extends PersonalContent{}





pred show{
	all p:PersonalProfile | #p.following >= 1
	all p:PersonalProfile | #p.friends >= 1

//	#Photo >5

	#PersonalProfile >= 2
//	#GroupProfile

}

run show for 10
